use super::DateTime;
use crate::format::StrftimeItems;
use crate::naive::{NaiveDate, NaiveTime};
use crate::offset::{FixedOffset, TimeZone, Utc};
#[cfg(feature = "clock")]
use crate::offset::{Local, Offset};
use crate::oldtime::Duration;
use crate::utils::{assert_debug_eq, assert_display_eq, WriteCompare};
use crate::{Datelike, Days, LocalResult, Months, NaiveDateTime, Timelike};

#[derive(Clone)]
struct DstTester;

impl DstTester {
    fn winter_offset() -> FixedOffset {
        FixedOffset::east_opt(8 * 60 * 60).unwrap()
    }
    fn summer_offset() -> FixedOffset {
        FixedOffset::east_opt(9 * 60 * 60).unwrap()
    }

    const TO_WINTER_MONTH_DAY: (u32, u32) = (4, 15);
    const TO_SUMMER_MONTH_DAY: (u32, u32) = (9, 15);

    fn transition_start_local() -> NaiveTime {
        NaiveTime::from_hms_opt(2, 0, 0).unwrap()
    }
}

impl TimeZone for DstTester {
    type Offset = FixedOffset;

    fn from_offset(_: &Self::Offset) -> Self {
        DstTester
    }

    fn offset_from_local_date(&self, _: &NaiveDate) -> crate::LocalResult<Self::Offset> {
        unimplemented!()
    }

    fn offset_from_local_datetime(
        &self,
        local: &NaiveDateTime,
    ) -> crate::LocalResult<Self::Offset> {
        let local_to_winter_transition_start = NaiveDate::from_ymd_opt(
            local.year(),
            DstTester::TO_WINTER_MONTH_DAY.0,
            DstTester::TO_WINTER_MONTH_DAY.1,
        )
        .unwrap()
        .and_time(DstTester::transition_start_local());

        let local_to_winter_transition_end = NaiveDate::from_ymd_opt(
            local.year(),
            DstTester::TO_WINTER_MONTH_DAY.0,
            DstTester::TO_WINTER_MONTH_DAY.1,
        )
        .unwrap()
        .and_time(DstTester::transition_start_local() - Duration::hours(1));

        let local_to_summer_transition_start = NaiveDate::from_ymd_opt(
            local.year(),
            DstTester::TO_SUMMER_MONTH_DAY.0,
            DstTester::TO_SUMMER_MONTH_DAY.1,
        )
        .unwrap()
        .and_time(DstTester::transition_start_local());

        let local_to_summer_transition_end = NaiveDate::from_ymd_opt(
            local.year(),
            DstTester::TO_SUMMER_MONTH_DAY.0,
            DstTester::TO_SUMMER_MONTH_DAY.1,
        )
        .unwrap()
        .and_time(DstTester::transition_start_local() + Duration::hours(1));

        if *local < local_to_winter_transition_end || *local >= local_to_summer_transition_end {
            LocalResult::Single(DstTester::summer_offset())
        } else if *local >= local_to_winter_transition_start
            && *local < local_to_summer_transition_start
        {
            LocalResult::Single(DstTester::winter_offset())
        } else if *local >= local_to_winter_transition_end
            && *local < local_to_winter_transition_start
        {
            LocalResult::Ambiguous(DstTester::winter_offset(), DstTester::summer_offset())
        } else if *local >= local_to_summer_transition_start
            && *local < local_to_summer_transition_end
        {
            LocalResult::None
        } else {
            panic!("Unexpected local time {}", local)
        }
    }

    fn offset_from_utc_date(&self, _: &NaiveDate) -> Self::Offset {
        unimplemented!()
    }

    fn offset_from_utc_datetime(&self, utc: &NaiveDateTime) -> Self::Offset {
        let utc_to_winter_transition = NaiveDate::from_ymd_opt(
            utc.year(),
            DstTester::TO_WINTER_MONTH_DAY.0,
            DstTester::TO_WINTER_MONTH_DAY.1,
        )
        .unwrap()
        .and_time(DstTester::transition_start_local())
            - DstTester::summer_offset();

        let utc_to_summer_transition = NaiveDate::from_ymd_opt(
            utc.year(),
            DstTester::TO_SUMMER_MONTH_DAY.0,
            DstTester::TO_SUMMER_MONTH_DAY.1,
        )
        .unwrap()
        .and_time(DstTester::transition_start_local())
            - DstTester::winter_offset();

        if *utc < utc_to_winter_transition || *utc >= utc_to_summer_transition {
            DstTester::summer_offset()
        } else if *utc >= utc_to_winter_transition && *utc < utc_to_summer_transition {
            DstTester::winter_offset()
        } else {
            panic!("Unexpected utc time {}", utc)
        }
    }
}

#[test]
fn test_datetime_add_days() {
    let est = FixedOffset::west_opt(5 * 60 * 60).unwrap();
    let kst = FixedOffset::east_opt(9 * 60 * 60).unwrap();

    assert_display_eq(
        est.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() + Days::new(5),
        "2014-05-11 07:08:09 -05:00",
    );
    assert_display_eq(
        kst.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() + Days::new(5),
        "2014-05-11 07:08:09 +09:00",
    );

    assert_display_eq(
        est.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() + Days::new(35),
        "2014-06-10 07:08:09 -05:00",
    );
    assert_display_eq(
        kst.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() + Days::new(35),
        "2014-06-10 07:08:09 +09:00",
    );

    assert_display_eq(
        DstTester.with_ymd_and_hms(2014, 4, 6, 7, 8, 9).unwrap() + Days::new(5),
        "2014-04-11 07:08:09 +09:00",
    );
    assert_display_eq(
        DstTester.with_ymd_and_hms(2014, 4, 6, 7, 8, 9).unwrap() + Days::new(10),
        "2014-04-16 07:08:09 +08:00",
    );

    assert_display_eq(
        DstTester.with_ymd_and_hms(2014, 9, 6, 7, 8, 9).unwrap() + Days::new(5),
        "2014-09-11 07:08:09 +08:00",
    );
    assert_display_eq(
        DstTester.with_ymd_and_hms(2014, 9, 6, 7, 8, 9).unwrap() + Days::new(10),
        "2014-09-16 07:08:09 +09:00",
    );
}

#[test]
fn test_datetime_sub_days() {
    let est = FixedOffset::west_opt(5 * 60 * 60).unwrap();
    let kst = FixedOffset::east_opt(9 * 60 * 60).unwrap();

    assert_display_eq(
        est.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() - Days::new(5),
        "2014-05-01 07:08:09 -05:00",
    );
    assert_display_eq(
        kst.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() - Days::new(5),
        "2014-05-01 07:08:09 +09:00",
    );

    assert_display_eq(
        est.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() - Days::new(35),
        "2014-04-01 07:08:09 -05:00",
    );
    assert_display_eq(
        kst.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() - Days::new(35),
        "2014-04-01 07:08:09 +09:00",
    );
}

#[test]
fn test_datetime_add_months() {
    let est = FixedOffset::west_opt(5 * 60 * 60).unwrap();
    let kst = FixedOffset::east_opt(9 * 60 * 60).unwrap();

    assert_display_eq(
        est.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() + Months::new(1),
        "2014-06-06 07:08:09 -05:00",
    );
    assert_display_eq(
        kst.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() + Months::new(1),
        "2014-06-06 07:08:09 +09:00",
    );

    assert_display_eq(
        est.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() + Months::new(5),
        "2014-10-06 07:08:09 -05:00",
    );
    assert_display_eq(
        kst.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() + Months::new(5),
        "2014-10-06 07:08:09 +09:00",
    );
}

#[test]
fn test_datetime_sub_months() {
    let est = FixedOffset::west_opt(5 * 60 * 60).unwrap();
    let kst = FixedOffset::east_opt(9 * 60 * 60).unwrap();

    assert_display_eq(
        est.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() - Months::new(1),
        "2014-04-06 07:08:09 -05:00",
    );
    assert_display_eq(
        kst.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() - Months::new(1),
        "2014-04-06 07:08:09 +09:00",
    );

    assert_display_eq(
        est.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() - Months::new(5),
        "2013-12-06 07:08:09 -05:00",
    );
    assert_display_eq(
        kst.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap() - Months::new(5),
        "2013-12-06 07:08:09 +09:00",
    );
}

#[test]
fn test_datetime_offset() {
    let est = FixedOffset::west_opt(5 * 60 * 60).unwrap();
    let edt = FixedOffset::west_opt(4 * 60 * 60).unwrap();
    let kst = FixedOffset::east_opt(9 * 60 * 60).unwrap();

    assert_display_eq(
        Utc.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap(),
        "2014-05-06 07:08:09 UTC",
    );
    assert_display_eq(
        edt.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap(),
        "2014-05-06 07:08:09 -04:00",
    );
    assert_display_eq(
        kst.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap(),
        "2014-05-06 07:08:09 +09:00",
    );
    assert_debug_eq(Utc.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap(), "2014-05-06T07:08:09Z");
    assert_debug_eq(
        edt.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap(),
        "2014-05-06T07:08:09-04:00",
    );
    assert_debug_eq(
        kst.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap(),
        "2014-05-06T07:08:09+09:00",
    );

    // edge cases
    assert_debug_eq(Utc.with_ymd_and_hms(2014, 5, 6, 0, 0, 0).unwrap(), "2014-05-06T00:00:00Z");
    assert_debug_eq(
        edt.with_ymd_and_hms(2014, 5, 6, 0, 0, 0).unwrap(),
        "2014-05-06T00:00:00-04:00",
    );
    assert_debug_eq(
        kst.with_ymd_and_hms(2014, 5, 6, 0, 0, 0).unwrap(),
        "2014-05-06T00:00:00+09:00",
    );
    assert_debug_eq(Utc.with_ymd_and_hms(2014, 5, 6, 23, 59, 59).unwrap(), "2014-05-06T23:59:59Z");
    assert_debug_eq(
        edt.with_ymd_and_hms(2014, 5, 6, 23, 59, 59).unwrap(),
        "2014-05-06T23:59:59-04:00",
    );
    assert_debug_eq(
        kst.with_ymd_and_hms(2014, 5, 6, 23, 59, 59).unwrap(),
        "2014-05-06T23:59:59+09:00",
    );

    let dt = Utc.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap();
    assert_eq!(dt, edt.with_ymd_and_hms(2014, 5, 6, 3, 8, 9).unwrap());
    assert_eq!(
        dt + Duration::seconds(3600 + 60 + 1),
        Utc.with_ymd_and_hms(2014, 5, 6, 8, 9, 10).unwrap()
    );
    assert_eq!(
        dt.signed_duration_since(edt.with_ymd_and_hms(2014, 5, 6, 10, 11, 12).unwrap()),
        Duration::seconds(-7 * 3600 - 3 * 60 - 3)
    );

    assert_eq!(*Utc.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap().offset(), Utc);
    assert_eq!(*edt.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap().offset(), edt);
    assert!(*edt.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap().offset() != est);
}

#[test]
#[allow(clippy::needless_borrow, clippy::op_ref)]
fn signed_duration_since_autoref() {
    let dt1 = Utc.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap();
    let dt2 = Utc.with_ymd_and_hms(2014, 3, 4, 5, 6, 7).unwrap();
    let diff1 = dt1.signed_duration_since(dt2); // Copy/consume
    let diff2 = dt2.signed_duration_since(&dt1); // Take by reference
    assert_eq!(diff1, -diff2);

    let diff1 = dt1 - &dt2; // We can choose to substract rhs by reference
    let diff2 = dt2 - dt1; // Or consume rhs
    assert_eq!(diff1, -diff2);
}

#[test]
fn test_datetime_date_and_time() {
    let tz = FixedOffset::east_opt(5 * 60 * 60).unwrap();
    let d = tz.with_ymd_and_hms(2014, 5, 6, 7, 8, 9).unwrap();
    assert_eq!(d.time(), NaiveTime::from_hms_opt(7, 8, 9).unwrap());
    assert_eq!(d.date_naive(), NaiveDate::from_ymd_opt(2014, 5, 6).unwrap());

    let tz = FixedOffset::east_opt(4 * 60 * 60).unwrap();
    let d = tz.with_ymd_and_hms(2016, 5, 4, 3, 2, 1).unwrap();
    assert_eq!(d.time(), NaiveTime::from_hms_opt(3, 2, 1).unwrap());
    assert_eq!(d.date_naive(), NaiveDate::from_ymd_opt(2016, 5, 4).unwrap());

    let tz = FixedOffset::west_opt(13 * 60 * 60).unwrap();
    let d = tz.with_ymd_and_hms(2017, 8, 9, 12, 34, 56).unwrap();
    assert_eq!(d.time(), NaiveTime::from_hms_opt(12, 34, 56).unwrap());
    assert_eq!(d.date_naive(), NaiveDate::from_ymd_opt(2017, 8, 9).unwrap());

    let utc_d = Utc.with_ymd_and_hms(2017, 8, 9, 12, 34, 56).unwrap();
    assert!(utc_d < d);
}

#[test]
#[cfg(feature = "clock")]
fn test_datetime_with_timezone() {
    let local_now = Local::now();
    let utc_now = local_now.with_timezone(&Utc);
    let local_now2 = utc_now.with_timezone(&Local);
    assert_eq!(local_now, local_now2);
}

#[test]
#[cfg(any(feature = "alloc", feature = "std"))]
fn test_datetime_rfc2822_and_rfc3339() {
    let edt = FixedOffset::east_opt(5 * 60 * 60).unwrap();
    assert_eq!(
        Utc.with_ymd_and_hms(2015, 2, 18, 23, 16, 9).unwrap().to_rfc2822(),
        "Wed, 18 Feb 2015 23:16:09 +0000"
    );
    assert_eq!(
        Utc.with_ymd_and_hms(2015, 2, 18, 23, 16, 9).unwrap().to_rfc3339(),
        "2015-02-18T23:16:09+00:00"
    );
    assert_eq!(
        edt.from_local_datetime(
            &NaiveDate::from_ymd_opt(2015, 2, 18)
                .unwrap()
                .and_hms_milli_opt(23, 16, 9, 150)
                .unwrap()
        )
        .unwrap()
        .to_rfc2822(),
        "Wed, 18 Feb 2015 23:16:09 +0500"
    );
    assert_eq!(
        edt.from_local_datetime(
            &NaiveDate::from_ymd_opt(2015, 2, 18)
                .unwrap()
                .and_hms_milli_opt(23, 16, 9, 150)
                .unwrap()
        )
        .unwrap()
        .to_rfc3339(),
        "2015-02-18T23:16:09.150+05:00"
    );
    assert_eq!(
        edt.from_local_datetime(
            &NaiveDate::from_ymd_opt(2015, 2, 18)
                .unwrap()
                .and_hms_micro_opt(23, 59, 59, 1_234_567)
                .unwrap()
        )
        .unwrap()
        .to_rfc2822(),
        "Wed, 18 Feb 2015 23:59:60 +0500"
    );
    assert_eq!(
        edt.from_local_datetime(
            &NaiveDate::from_ymd_opt(2015, 2, 18)
                .unwrap()
                .and_hms_micro_opt(23, 59, 59, 1_234_567)
                .unwrap()
        )
        .unwrap()
        .to_rfc3339(),
        "2015-02-18T23:59:60.234567+05:00"
    );

    assert_eq!(
        DateTime::parse_from_rfc2822("Wed, 18 Feb 2015 23:16:09 +0000"),
        Ok(FixedOffset::east_opt(0).unwrap().with_ymd_and_hms(2015, 2, 18, 23, 16, 9).unwrap())
    );
    assert_eq!(
        DateTime::parse_from_rfc2822("Wed, 18 Feb 2015 23:16:09 -0000"),
        Ok(FixedOffset::east_opt(0).unwrap().with_ymd_and_hms(2015, 2, 18, 23, 16, 9).unwrap())
    );
    assert_eq!(
        DateTime::parse_from_rfc3339("2015-02-18T23:16:09Z"),
        Ok(FixedOffset::east_opt(0).unwrap().with_ymd_and_hms(2015, 2, 18, 23, 16, 9).unwrap())
    );
    assert_eq!(
        DateTime::parse_from_rfc2822("Wed, 18 Feb 2015 23:59:60 +0500"),
        Ok(edt
            .from_local_datetime(
                &NaiveDate::from_ymd_opt(2015, 2, 18)
                    .unwrap()
                    .and_hms_milli_opt(23, 59, 59, 1_000)
                    .unwrap()
            )
            .unwrap())
    );
    assert!(DateTime::parse_from_rfc2822("31 DEC 262143 23:59 -2359").is_err());
    assert_eq!(
        DateTime::parse_from_rfc3339("2015-02-18T23:59:60.234567+05:00"),
        Ok(edt
            .from_local_datetime(
                &NaiveDate::from_ymd_opt(2015, 2, 18)
                    .unwrap()
                    .and_hms_micro_opt(23, 59, 59, 1_234_567)
                    .unwrap()
            )
            .unwrap())
    );
}

#[test]
#[cfg(any(feature = "alloc", feature = "std"))]
fn test_rfc3339_opts() {
    use crate::SecondsFormat::*;
    let pst = FixedOffset::east_opt(8 * 60 * 60).unwrap();
    let dt = pst
        .from_local_datetime(
            &NaiveDate::from_ymd_opt(2018, 1, 11)
                .unwrap()
                .and_hms_nano_opt(10, 5, 13, 84_660_000)
                .unwrap(),
        )
        .unwrap();
    assert_eq!(dt.to_rfc3339_opts(Secs, false), "2018-01-11T10:05:13+08:00");
    assert_eq!(dt.to_rfc3339_opts(Secs, true), "2018-01-11T10:05:13+08:00");
    assert_eq!(dt.to_rfc3339_opts(Millis, false), "2018-01-11T10:05:13.084+08:00");
    assert_eq!(dt.to_rfc3339_opts(Micros, false), "2018-01-11T10:05:13.084660+08:00");
    assert_eq!(dt.to_rfc3339_opts(Nanos, false), "2018-01-11T10:05:13.084660000+08:00");
    assert_eq!(dt.to_rfc3339_opts(AutoSi, false), "2018-01-11T10:05:13.084660+08:00");

    let ut = DateTime::<Utc>::from_utc(dt.naive_utc(), Utc);
    assert_eq!(ut.to_rfc3339_opts(Secs, false), "2018-01-11T02:05:13+00:00");
    assert_eq!(ut.to_rfc3339_opts(Secs, true), "2018-01-11T02:05:13Z");
    assert_eq!(ut.to_rfc3339_opts(Millis, false), "2018-01-11T02:05:13.084+00:00");
    assert_eq!(ut.to_rfc3339_opts(Millis, true), "2018-01-11T02:05:13.084Z");
    assert_eq!(ut.to_rfc3339_opts(Micros, true), "2018-01-11T02:05:13.084660Z");
    assert_eq!(ut.to_rfc3339_opts(Nanos, true), "2018-01-11T02:05:13.084660000Z");
    assert_eq!(ut.to_rfc3339_opts(AutoSi, true), "2018-01-11T02:05:13.084660Z");
}

#[test]
#[should_panic]
#[cfg(any(feature = "alloc", feature = "std"))]
fn test_rfc3339_opts_nonexhaustive() {
    use crate::SecondsFormat;
    let dt = Utc.with_ymd_and_hms(1999, 10, 9, 1, 2, 3).unwrap();
    let _ = dt.to_rfc3339_opts(SecondsFormat::__NonExhaustive, true);
}

#[test]
fn test_datetime_from_str() {
    assert_eq!(
        "2015-02-18T23:16:9.15Z".parse::<DateTime<FixedOffset>>(),
        Ok(FixedOffset::east_opt(0)
            .unwrap()
            .from_local_datetime(
                &NaiveDate::from_ymd_opt(2015, 2, 18)
                    .unwrap()
                    .and_hms_milli_opt(23, 16, 9, 150)
                    .unwrap()
            )
            .unwrap())
    );
    assert_eq!(
        "2015-02-18T23:16:9.15Z".parse::<DateTime<Utc>>(),
        Ok(Utc
            .from_local_datetime(
                &NaiveDate::from_ymd_opt(2015, 2, 18)
                    .unwrap()
                    .and_hms_milli_opt(23, 16, 9, 150)
                    .unwrap()
            )
            .unwrap())
    );
    assert_eq!(
        "2015-02-18T23:16:9.15 UTC".parse::<DateTime<Utc>>(),
        Ok(Utc
            .from_local_datetime(
                &NaiveDate::from_ymd_opt(2015, 2, 18)
                    .unwrap()
                    .and_hms_milli_opt(23, 16, 9, 150)
                    .unwrap()
            )
            .unwrap())
    );
    assert_eq!(
        "2015-02-18T23:16:9.15UTC".parse::<DateTime<Utc>>(),
        Ok(Utc
            .from_local_datetime(
                &NaiveDate::from_ymd_opt(2015, 2, 18)
                    .unwrap()
                    .and_hms_milli_opt(23, 16, 9, 150)
                    .unwrap()
            )
            .unwrap())
    );

    assert_eq!(
        "2015-2-18T23:16:9.15Z".parse::<DateTime<FixedOffset>>(),
        Ok(FixedOffset::east_opt(0)
            .unwrap()
            .from_local_datetime(
                &NaiveDate::from_ymd_opt(2015, 2, 18)
                    .unwrap()
                    .and_hms_milli_opt(23, 16, 9, 150)
                    .unwrap()
            )
            .unwrap())
    );
    assert_eq!(
        "2015-2-18T13:16:9.15-10:00".parse::<DateTime<FixedOffset>>(),
        Ok(FixedOffset::west_opt(10 * 3600)
            .unwrap()
            .from_local_datetime(
                &NaiveDate::from_ymd_opt(2015, 2, 18)
                    .unwrap()
                    .and_hms_milli_opt(13, 16, 9, 150)
                    .unwrap()
            )
            .unwrap())
    );
    assert!("2015-2-18T23:16:9.15".parse::<DateTime<FixedOffset>>().is_err());

    assert_eq!(
        "2015-2-18T23:16:9.15Z".parse::<DateTime<Utc>>(),
        Ok(Utc
            .from_local_datetime(
                &NaiveDate::from_ymd_opt(2015, 2, 18)
                    .unwrap()
                    .and_hms_milli_opt(23, 16, 9, 150)
                    .unwrap()
            )
            .unwrap())
    );
    assert_eq!(
        "2015-2-18T13:16:9.15-10:00".parse::<DateTime<Utc>>(),
        Ok(Utc
            .from_local_datetime(
                &NaiveDate::from_ymd_opt(2015, 2, 18)
                    .unwrap()
                    .and_hms_milli_opt(23, 16, 9, 150)
                    .unwrap()
            )
            .unwrap())
    );
    assert!("2015-2-18T23:16:9.15".parse::<DateTime<Utc>>().is_err());

    // no test for `DateTime<Local>`, we cannot verify that much.
}

#[test]
fn test_datetime_parse_from_str() {
    let ymdhms = |y, m, d, h, n, s, off| {
        FixedOffset::east_opt(off).unwrap().with_ymd_and_hms(y, m, d, h, n, s).unwrap()
    };
    assert_eq!(
        DateTime::parse_from_str("2014-5-7T12:34:56+09:30", "%Y-%m-%dT%H:%M:%S%z"),
        Ok(ymdhms(2014, 5, 7, 12, 34, 56, 570 * 60))
    ); // ignore offset
    assert!(DateTime::parse_from_str("20140507000000", "%Y%m%d%H%M%S").is_err()); // no offset
    assert!(DateTime::parse_from_str("Fri, 09 Aug 2013 23:54:35 GMT", "%a, %d %b %Y %H:%M:%S GMT")
        .is_err());
    assert_eq!(
        Utc.datetime_from_str("Fri, 09 Aug 2013 23:54:35 GMT", "%a, %d %b %Y %H:%M:%S GMT"),
        Ok(Utc.with_ymd_and_hms(2013, 8, 9, 23, 54, 35).unwrap())
    );
    assert_eq!(
        DateTime::parse_from_str("0", "%s").unwrap(),
        NaiveDateTime::from_timestamp_opt(0, 0).unwrap().and_utc().fixed_offset()
    );
}

#[test]
#[cfg(any(feature = "alloc", feature = "std"))]
fn test_to_string_round_trip() {
    let dt = Utc.with_ymd_and_hms(2000, 1, 1, 0, 0, 0).unwrap();
    let _dt: DateTime<Utc> = dt.to_string().parse().unwrap();

    let ndt_fixed = dt.with_timezone(&FixedOffset::east_opt(3600).unwrap());
    let _dt: DateTime<FixedOffset> = ndt_fixed.to_string().parse().unwrap();

    let ndt_fixed = dt.with_timezone(&FixedOffset::east_opt(0).unwrap());
    let _dt: DateTime<FixedOffset> = ndt_fixed.to_string().parse().unwrap();
}

#[test]
#[cfg(feature = "clock")]
fn test_to_string_round_trip_with_local() {
    let ndt = Local::now();
    let _dt: DateTime<FixedOffset> = ndt.to_string().parse().unwrap();
}

#[test]
#[cfg(feature = "clock")]
fn test_datetime_format_with_local() {
    // if we are not around the year boundary, local and UTC date should have the same year
    let dt = Local::now().with_month(5).unwrap();
    assert_eq!(dt.format_to_string("%Y"), dt.with_timezone(&Utc).format_to_string("%Y"));
}

#[test]
fn test_datetime_is_send_and_copy() {
    fn _assert_send_copy<T: Send + Copy>() {}
    // UTC is known to be `Send + Copy`.
    _assert_send_copy::<DateTime<Utc>>();
}

#[test]
fn test_subsecond_part() {
    let datetime = Utc
        .from_local_datetime(
            &NaiveDate::from_ymd_opt(2014, 7, 8)
                .unwrap()
                .and_hms_nano_opt(9, 10, 11, 1234567)
                .unwrap(),
        )
        .unwrap();

    assert_eq!(1, datetime.timestamp_subsec_millis());
    assert_eq!(1234, datetime.timestamp_subsec_micros());
    assert_eq!(1234567, datetime.timestamp_subsec_nanos());
}

#[test]
#[cfg(feature = "std")]
fn test_from_system_time() {
    use std::time::{Duration, SystemTime, UNIX_EPOCH};

    let nanos = 999_999_000;

    let epoch = Utc.with_ymd_and_hms(1970, 1, 1, 0, 0, 0).unwrap();

    // SystemTime -> DateTime<Utc>
    assert_eq!(DateTime::<Utc>::from(UNIX_EPOCH), epoch);
    assert_eq!(
        DateTime::<Utc>::from(UNIX_EPOCH + Duration::new(999_999_999, nanos)),
        Utc.from_local_datetime(
            &NaiveDate::from_ymd_opt(2001, 9, 9)
                .unwrap()
                .and_hms_nano_opt(1, 46, 39, nanos)
                .unwrap()
        )
        .unwrap()
    );
    assert_eq!(
        DateTime::<Utc>::from(UNIX_EPOCH - Duration::new(999_999_999, nanos)),
        Utc.from_local_datetime(
            &NaiveDate::from_ymd_opt(1938, 4, 24)
                .unwrap()
                .and_hms_nano_opt(22, 13, 20, 1_000)
                .unwrap()
        )
        .unwrap()
    );

    // DateTime<Utc> -> SystemTime
    assert_eq!(SystemTime::from(epoch), UNIX_EPOCH);
    assert_eq!(
        SystemTime::from(
            Utc.from_local_datetime(
                &NaiveDate::from_ymd_opt(2001, 9, 9)
                    .unwrap()
                    .and_hms_nano_opt(1, 46, 39, nanos)
                    .unwrap()
            )
            .unwrap()
        ),
        UNIX_EPOCH + Duration::new(999_999_999, nanos)
    );
    assert_eq!(
        SystemTime::from(
            Utc.from_local_datetime(
                &NaiveDate::from_ymd_opt(1938, 4, 24)
                    .unwrap()
                    .and_hms_nano_opt(22, 13, 20, 1_000)
                    .unwrap()
            )
            .unwrap()
        ),
        UNIX_EPOCH - Duration::new(999_999_999, nanos)
    );

    // DateTime<any tz> -> SystemTime (via `with_timezone`)
    #[cfg(feature = "clock")]
    {
        assert_eq!(SystemTime::from(epoch.with_timezone(&Local)), UNIX_EPOCH);
    }
    assert_eq!(
        SystemTime::from(epoch.with_timezone(&FixedOffset::east_opt(32400).unwrap())),
        UNIX_EPOCH
    );
    assert_eq!(
        SystemTime::from(epoch.with_timezone(&FixedOffset::west_opt(28800).unwrap())),
        UNIX_EPOCH
    );
}

#[test]
fn test_datetime_format_alignment() {
    use core::fmt::Write;

    let datetime =
        Utc.with_ymd_and_hms(2007, 1, 2, 12, 34, 56).unwrap().with_nanosecond(123456789).unwrap();

    // Item::Literal
    let formatter = DateTime::formatter(StrftimeItems::new("%%")).unwrap();
    let percent = datetime.format_with(&formatter);
    write!(&mut WriteCompare::new("   %"), "{:>4}", percent).unwrap();
    write!(&mut WriteCompare::new("%   "), "{:<4}", percent).unwrap();
    write!(&mut WriteCompare::new(" %  "), "{:^4}", percent).unwrap();

    // Item::Numeric
    let formatter = DateTime::formatter(StrftimeItems::new("%Y")).unwrap();
    let year = datetime.format_with(&formatter);
    write!(&mut WriteCompare::new("——2007"), "{:—>6}", year).unwrap();
    write!(&mut WriteCompare::new("2007——"), "{:—<6}", year).unwrap();
    write!(&mut WriteCompare::new("—2007—"), "{:—^6}", year).unwrap();

    // Item::Fixed
    let formatter = DateTime::formatter(StrftimeItems::new("%Z")).unwrap();
    let tz = datetime.format_with(&formatter);
    write!(&mut WriteCompare::new("  UTC"), "{:>5}", tz).unwrap();
    write!(&mut WriteCompare::new("UTC  "), "{:<5}", tz).unwrap();
    write!(&mut WriteCompare::new(" UTC "), "{:^5}", tz).unwrap();

    // [Item::Numeric, Item::Space, Item::Literal, Item::Space, Item::Numeric]
    let formatter = DateTime::formatter(StrftimeItems::new("%Y %B %d")).unwrap();
    let ymd = datetime.format_with(&formatter);
    write!(&mut WriteCompare::new("  2007 January 02"), "{:>17}", ymd).unwrap();
    write!(&mut WriteCompare::new("2007 January 02  "), "{:<17}", ymd).unwrap();
    write!(&mut WriteCompare::new(" 2007 January 02 "), "{:^17}", ymd).unwrap();

    // Truncated
    let formatter = DateTime::formatter(StrftimeItems::new("%T%.6f")).unwrap();
    let time = datetime.format_with(&formatter);
    write!(&mut WriteCompare::new("12:34:56.1234"), "{:.13}", time).unwrap();
}

#[test]
fn test_datetime_from_local() {
    // 2000-01-12T02:00:00Z
    let naivedatetime_utc =
        NaiveDate::from_ymd_opt(2000, 1, 12).unwrap().and_hms_opt(2, 0, 0).unwrap();
    let datetime_utc = DateTime::<Utc>::from_utc(naivedatetime_utc, Utc);

    // 2000-01-12T10:00:00+8:00:00
    let timezone_east = FixedOffset::east_opt(8 * 60 * 60).unwrap();
    let naivedatetime_east =
        NaiveDate::from_ymd_opt(2000, 1, 12).unwrap().and_hms_opt(10, 0, 0).unwrap();
    let datetime_east = DateTime::<FixedOffset>::from_local(naivedatetime_east, timezone_east);

    // 2000-01-11T19:00:00-7:00:00
    let timezone_west = FixedOffset::west_opt(7 * 60 * 60).unwrap();
    let naivedatetime_west =
        NaiveDate::from_ymd_opt(2000, 1, 11).unwrap().and_hms_opt(19, 0, 0).unwrap();
    let datetime_west = DateTime::<FixedOffset>::from_local(naivedatetime_west, timezone_west);

    assert_eq!(datetime_east, datetime_utc.with_timezone(&timezone_east));
    assert_eq!(datetime_west, datetime_utc.with_timezone(&timezone_west));
}

#[test]
#[cfg(feature = "clock")]
fn test_years_elapsed() {
    const WEEKS_PER_YEAR: f32 = 52.1775;

    // This is always at least one year because 1 year = 52.1775 weeks.
    let one_year_ago =
        Utc::now().date_naive() - Duration::weeks((WEEKS_PER_YEAR * 1.5).ceil() as i64);
    // A bit more than 2 years.
    let two_year_ago =
        Utc::now().date_naive() - Duration::weeks((WEEKS_PER_YEAR * 2.5).ceil() as i64);

    assert_eq!(Utc::now().date_naive().years_since(one_year_ago), Some(1));
    assert_eq!(Utc::now().date_naive().years_since(two_year_ago), Some(2));

    // If the given DateTime is later than now, the function will always return 0.
    let future = Utc::now().date_naive() + Duration::weeks(12);
    assert_eq!(Utc::now().date_naive().years_since(future), None);
}

#[test]
fn test_datetime_add_assign() {
    let naivedatetime = NaiveDate::from_ymd_opt(2000, 1, 1).unwrap().and_hms_opt(0, 0, 0).unwrap();
    let datetime = DateTime::<Utc>::from_utc(naivedatetime, Utc);
    let mut datetime_add = datetime;

    datetime_add += Duration::seconds(60);
    assert_eq!(datetime_add, datetime + Duration::seconds(60));

    let timezone = FixedOffset::east_opt(60 * 60).unwrap();
    let datetime = datetime.with_timezone(&timezone);
    let datetime_add = datetime_add.with_timezone(&timezone);

    assert_eq!(datetime_add, datetime + Duration::seconds(60));

    let timezone = FixedOffset::west_opt(2 * 60 * 60).unwrap();
    let datetime = datetime.with_timezone(&timezone);
    let datetime_add = datetime_add.with_timezone(&timezone);

    assert_eq!(datetime_add, datetime + Duration::seconds(60));
}

#[test]
#[cfg(feature = "clock")]
fn test_datetime_add_assign_local() {
    let naivedatetime = NaiveDate::from_ymd_opt(2022, 1, 1).unwrap().and_hms_opt(0, 0, 0).unwrap();

    let datetime = Local.from_utc_datetime(&naivedatetime);
    let mut datetime_add = Local.from_utc_datetime(&naivedatetime);

    // ensure we cross a DST transition
    for i in 1..=365 {
        datetime_add += Duration::days(1);
        assert_eq!(datetime_add, datetime + Duration::days(i))
    }
}

#[test]
fn test_datetime_sub_assign() {
    let naivedatetime = NaiveDate::from_ymd_opt(2000, 1, 1).unwrap().and_hms_opt(12, 0, 0).unwrap();
    let datetime = DateTime::<Utc>::from_utc(naivedatetime, Utc);
    let mut datetime_sub = datetime;

    datetime_sub -= Duration::minutes(90);
    assert_eq!(datetime_sub, datetime - Duration::minutes(90));

    let timezone = FixedOffset::east_opt(60 * 60).unwrap();
    let datetime = datetime.with_timezone(&timezone);
    let datetime_sub = datetime_sub.with_timezone(&timezone);

    assert_eq!(datetime_sub, datetime - Duration::minutes(90));

    let timezone = FixedOffset::west_opt(2 * 60 * 60).unwrap();
    let datetime = datetime.with_timezone(&timezone);
    let datetime_sub = datetime_sub.with_timezone(&timezone);

    assert_eq!(datetime_sub, datetime - Duration::minutes(90));
}

#[test]
#[cfg(feature = "clock")]
fn test_datetime_sub_assign_local() {
    let naivedatetime = NaiveDate::from_ymd_opt(2022, 1, 1).unwrap().and_hms_opt(0, 0, 0).unwrap();

    let datetime = Local.from_utc_datetime(&naivedatetime);
    let mut datetime_sub = Local.from_utc_datetime(&naivedatetime);

    // ensure we cross a DST transition
    for i in 1..=365 {
        datetime_sub -= Duration::days(1);
        assert_eq!(datetime_sub, datetime - Duration::days(i))
    }
}

#[test]
#[cfg(all(target_os = "windows", feature = "clock"))]
fn test_from_naive_date_time_windows() {
    let min_year = NaiveDate::from_ymd_opt(1601, 1, 3).unwrap().and_hms_opt(0, 0, 0).unwrap();

    let max_year = NaiveDate::from_ymd_opt(30827, 12, 29).unwrap().and_hms_opt(23, 59, 59).unwrap();

    let too_low_year =
        NaiveDate::from_ymd_opt(1600, 12, 29).unwrap().and_hms_opt(23, 59, 59).unwrap();

    let too_high_year = NaiveDate::from_ymd_opt(30829, 1, 3).unwrap().and_hms_opt(0, 0, 0).unwrap();

    let _ = Local.from_utc_datetime(&min_year);
    let _ = Local.from_utc_datetime(&max_year);

    let _ = Local.from_local_datetime(&min_year);
    let _ = Local.from_local_datetime(&max_year);

    let local_too_low = Local.from_local_datetime(&too_low_year);
    let local_too_high = Local.from_local_datetime(&too_high_year);

    assert_eq!(local_too_low, LocalResult::None);
    assert_eq!(local_too_high, LocalResult::None);

    let err = std::panic::catch_unwind(|| {
        Local.from_utc_datetime(&too_low_year);
    });
    assert!(err.is_err());

    let err = std::panic::catch_unwind(|| {
        Local.from_utc_datetime(&too_high_year);
    });
    assert!(err.is_err());
}

#[test]
#[cfg(feature = "clock")]
fn test_datetime_local_from_preserves_offset() {
    let naivedatetime = NaiveDate::from_ymd_opt(2023, 1, 1).unwrap().and_hms_opt(0, 0, 0).unwrap();

    let datetime = Local.from_utc_datetime(&naivedatetime);
    let offset = datetime.offset().fix();

    let datetime_fixed: DateTime<FixedOffset> = datetime.into();
    assert_eq!(&offset, datetime_fixed.offset());
    assert_eq!(datetime.fixed_offset(), datetime_fixed);
}

#[test]
fn test_datetime_fixed_offset() {
    let naivedatetime = NaiveDate::from_ymd_opt(2023, 1, 1).unwrap().and_hms_opt(0, 0, 0).unwrap();

    let datetime = Utc.from_utc_datetime(&naivedatetime);
    let fixed_utc = FixedOffset::east_opt(0).unwrap();
    assert_eq!(datetime.fixed_offset(), fixed_utc.from_local_datetime(&naivedatetime).unwrap());

    let fixed_offset = FixedOffset::east_opt(3600).unwrap();
    let datetime_fixed = fixed_offset.from_local_datetime(&naivedatetime).unwrap();
    assert_eq!(datetime_fixed.fixed_offset(), datetime_fixed);
}

#[test]
fn test_add_sub_months() {
    let utc_dt = Utc.with_ymd_and_hms(2018, 9, 5, 23, 58, 0).unwrap();
    assert_eq!(utc_dt + Months::new(15), Utc.with_ymd_and_hms(2019, 12, 5, 23, 58, 0).unwrap());

    let utc_dt = Utc.with_ymd_and_hms(2020, 1, 31, 23, 58, 0).unwrap();
    assert_eq!(utc_dt + Months::new(1), Utc.with_ymd_and_hms(2020, 2, 29, 23, 58, 0).unwrap());
    assert_eq!(utc_dt + Months::new(2), Utc.with_ymd_and_hms(2020, 3, 31, 23, 58, 0).unwrap());

    let utc_dt = Utc.with_ymd_and_hms(2018, 9, 5, 23, 58, 0).unwrap();
    assert_eq!(utc_dt - Months::new(15), Utc.with_ymd_and_hms(2017, 6, 5, 23, 58, 0).unwrap());

    let utc_dt = Utc.with_ymd_and_hms(2020, 3, 31, 23, 58, 0).unwrap();
    assert_eq!(utc_dt - Months::new(1), Utc.with_ymd_and_hms(2020, 2, 29, 23, 58, 0).unwrap());
    assert_eq!(utc_dt - Months::new(2), Utc.with_ymd_and_hms(2020, 1, 31, 23, 58, 0).unwrap());
}

#[test]
fn test_auto_conversion() {
    let utc_dt = Utc.with_ymd_and_hms(2018, 9, 5, 23, 58, 0).unwrap();
    let cdt_dt = FixedOffset::west_opt(5 * 60 * 60)
        .unwrap()
        .with_ymd_and_hms(2018, 9, 5, 18, 58, 0)
        .unwrap();
    let utc_dt2: DateTime<Utc> = cdt_dt.into();
    assert_eq!(utc_dt, utc_dt2);
}
