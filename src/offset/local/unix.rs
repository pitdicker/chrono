// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::{cell::RefCell, collections::hash_map, env, fs, hash::Hasher, time::SystemTime};

use super::tz_info::TimeZone;
use super::{FixedOffset, NaiveDateTime};
use crate::{Datelike, MappedLocalTime};

pub(super) fn offset_from_utc_datetime(utc: &NaiveDateTime) -> MappedLocalTime<FixedOffset> {
    offset(utc, false)
}

pub(super) fn offset_from_local_datetime(local: &NaiveDateTime) -> MappedLocalTime<FixedOffset> {
    offset(local, true)
}

fn offset(d: &NaiveDateTime, local: bool) -> MappedLocalTime<FixedOffset> {
    TZ_INFO.with(|maybe_cache| {
        maybe_cache.borrow_mut().offset(*d, local)
    })
}

thread_local! {
    static TZ_INFO: RefCell<Cache> = const { RefCell::new(
        Cache {
            zone: None,
            source: Source::Uninitialized,
            last_checked: SystemTime::UNIX_EPOCH,
        }
    ) };
}

#[derive(PartialEq)]
enum Source {
    Environment { hash: u64 },
    LocalTime,
    Uninitialized,
}

impl Source {
    fn new(env_tz: Option<&str>) -> Source {
        match env_tz {
            Some(tz) => {
                let mut hasher = hash_map::DefaultHasher::new();
                hasher.write(tz.as_bytes());
                let hash = hasher.finish();
                Source::Environment { hash }
            }
            None => Source::LocalTime,
        }
    }
}

struct Cache {
    zone: Option<TimeZone>,
    source: Source,
    last_checked: SystemTime,
}

#[cfg(target_os = "aix")]
const TZDB_LOCATION: &str = "/usr/share/lib/zoneinfo";

#[cfg(not(any(target_os = "android", target_os = "aix")))]
const TZDB_LOCATION: &str = "/usr/share/zoneinfo";

fn fallback_timezone() -> Option<TimeZone> {
    let tz_name = iana_time_zone::get_timezone().ok()?;
    #[cfg(not(target_os = "android"))]
    let bytes = fs::read(format!("{}/{}", TZDB_LOCATION, tz_name)).ok()?;
    #[cfg(target_os = "android")]
    let bytes = android_tzdata::find_tz_data(&tz_name).ok()?;
    TimeZone::from_tz_data(&bytes).ok()
}

fn current_zone(var: Option<&str>) -> TimeZone {
    TimeZone::local(var).ok().or_else(fallback_timezone).unwrap_or_else(TimeZone::utc)
}

impl Cache {
    fn offset(&mut self, d: NaiveDateTime, local: bool) -> MappedLocalTime<FixedOffset> {
        self.refresh_cache();

        if !local {
            let offset = self
                .zone
                .as_ref()
                .unwrap()
                .find_local_time_type(d.and_utc().timestamp())
                .expect("unable to select local time type")
                .offset();

            return match FixedOffset::east_opt(offset) {
                Some(offset) => MappedLocalTime::Single(offset),
                None => MappedLocalTime::None,
            };
        }

        // we pass through the year as the year of a local point in time must either be valid in that locale, or
        // the entire time was skipped in which case we will return MappedLocalTime::None anyway.
        self.zone
            .as_ref()
            .unwrap()
            .find_local_time_type_from_local(d.and_utc().timestamp(), d.year())
            .expect("unable to select local time type")
            .and_then(|o| FixedOffset::east_opt(o.offset()))
    }

    // Refresh our cached data if necessary.
    //
    // If the cache has been around for less than a second then we reuse it unconditionally. This is
    // a reasonable tradeoff because the timezone generally won't be changing _that_ often, but if
    // the time zone does change, it will reflect sufficiently quickly from an application user's
    // perspective.
    fn refresh_cache(&mut self) {
        let now = SystemTime::now();
        if let Ok(d) = now.duration_since(self.last_checked) {
            if d.as_secs() < 1 && self.source != Source::Uninitialized {
                return;
            }
        }

        if self.needs_update() {
            let env_tz = env::var("TZ").ok();
            let env_ref = env_tz.as_deref();
            self.source = Source::new(env_ref);
            self.zone = Some(current_zone(env_ref));
        }
        self.last_checked = now;
    }

    /// Check if any of the `TZ` environment variable or `/etc/localtime` have changed.
    fn needs_update(&self) -> bool {
        let env_tz = env::var("TZ").ok();
        let env_ref = env_tz.as_deref();
        let new_source = Source::new(env_ref);

        match (&self.source, &new_source) {
            (Source::Environment { hash: old_hash }, Source::Environment { hash })
                if old_hash == hash =>
            {
                false
            }
            (Source::LocalTime, Source::LocalTime) => {
                match fs::symlink_metadata("/etc/localtime").and_then(|m| m.modified()) {
                    Ok(mtime) => mtime > self.last_checked,
                    Err(_) => false,
                }
            }
            _ => true,
        }
    }
}
