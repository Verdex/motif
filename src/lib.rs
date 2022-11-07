#[derive(Debug)]
pub enum MatchError {
    Error(usize),
    ErrorEndOfFile,
    Fatal(usize), 
    FatalEndOfFile,
}

impl std::fmt::Display for MatchError {
    fn fmt(&self, f : &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            MatchError::Error(x) => write!(f, "encountered error at:  {}", x),
            MatchError::ErrorEndOfFile => write!(f, "encountered end of file error"),
            MatchError::Fatal(x) => write!(f, "encountered fatal error at:  {}", x),
            MatchError::FatalEndOfFile => write!(f, "encountered fatal end of file" ),
        }
    }
}

impl std::error::Error for MatchError {}

#[macro_export]
macro_rules! alt {
    ($matcher_name:ident<$life:lifetime> : $t_in:ty => $t_out:ty = $($m:ident)|+ => |$name:ident| $b:block) => {
        fn $matcher_name<$life>(input : &mut (impl Iterator<Item = (usize, $t_in)> + Clone)) -> Result<$t_out, MatchError> {

            let mut _error : Option<MatchError> = None;

            $(
                match $m(input) {
                    Ok(v) => { 
                        let $name = v;
                        let ret = $b;
                        return Ok(ret); 
                    },
                    e @ Err(MatchError::Fatal(_)) => { return e; },
                    e @ Err(MatchError::FatalEndOfFile) => { return e; },
                    Err(e @ MatchError::Error(_)) => { _error = Some(e); },
                    Err(e @ MatchError::ErrorEndOfFile) => { _error = Some(e); },
                }

            )*
        
            Err(_error.unwrap())
        }
    };
    ($matcher_name:ident<$life:lifetime> : $t:ty = $($m:ident)|+ => |$name:ident| $b:block) => {
        alt!($matcher_name<$life> : $t => $t = $($m)|+ => |$name| $b);
    };
    ($matcher_name:ident : $t:ty = $($m:ident)|+ => |$name:ident| $b:block) => {
        alt!($matcher_name<'a> : $t => $t = $($m)|+ => |$name| $b);
    };
    ($matcher_name:ident : $t_in:ty => $t_out:ty = $($m:ident)|+ => |$name:ident| $b:block) => {
        alt!($matcher_name<'a> : $t_in => $t_out = $($m)|+ => |$name| $b);
    };
    ($matcher_name:ident<$life:lifetime> : $t_in:ty => $t_out:ty = $($m:ident)|+) => {
        alt!($matcher_name<$life> : $t_in => $t_out = $($m)|+ => |x| { x });
    };
    ($matcher_name:ident<$life:lifetime> : $t:ty = $($m:ident)|+) => {
        alt!($matcher_name<$life> : $t => $t = $($m)|+ => |x| { x });
    };
    ($matcher_name:ident : $t:ty = $($m:ident)|+) => {
        alt!($matcher_name<'a> : $t => $t = $($m)|+ => |x| { x });
    };
    ($matcher_name:ident : $t_in:ty => $t_out:ty = $($m:ident)|+) => {
        alt!($matcher_name<'a> : $t_in => $t_out = $($m)|+ => |x| { x });
    };
}

#[macro_export]
macro_rules! group { 
    ($matcher_name:ident<$life:lifetime> : $t_in:ty => $t_out:ty = |$input:ident| $b:block) => {
        fn $matcher_name<$life>($input : &mut (impl Iterator<Item = (usize, $t_in)> + Clone)) -> Result<$t_out, MatchError> {
            $b
        }
    };
    ($matcher_name:ident<$life:lifetime> : $t:ty = |$input:ident| $b:block) => {
        group!($matcher_name<$life>: $t => $t = |$input| $b);
    };
    ($matcher_name:ident: $t:ty = |$input:ident| $b:block) => {
        group!($matcher_name<'a>: $t => $t = |$input| $b);
    };
    ($matcher_name:ident: $t_in:ty => $t_out:ty = |$input:ident| $b:block) => {
        group!($matcher_name<'a>: $t_in => $t_out = |$input| $b);
    };
}

#[macro_export]
macro_rules! pred {
    ($matcher_name:ident<$life:lifetime> : $t_in:ty => $t_out:ty = |$item:ident| $predicate:expr => $b:block) => {
        #[allow(unused_variables)]
        fn $matcher_name<$life>(input : &mut (impl Iterator<Item = (usize, $t_in)> + Clone)) -> Result<$t_out, MatchError> {

            let mut rp = input.clone();

            let p = |$item:$t_in| $predicate;
            
            match input.next() {
                Some((_, c)) if p(c) => {
                    let $item = c;
                    let ret = $b;
                    Ok(ret)
                },
                Some((i, _)) => { 
                    std::mem::swap(&mut rp, input);
                    Err(MatchError::Error(i))
                },
                None => {
                    std::mem::swap(&mut rp, input);
                    Err(MatchError::ErrorEndOfFile)
                },
            } 
        }
    };
    ($matcher_name:ident : $t_in:ty => $t_out:ty = |$item:ident| $predicate:expr => $b:block) => {
        pred!($matcher_name<'a> : $t_in => $t_out = |$item| $predicate => $b);
    };
    ($matcher_name:ident<$life:lifetime> : $t:ty = |$item:ident| $predicate:expr) => {
        pred!($matcher_name<$life> : $t => $t = |$item| $predicate => { $item });
    };
    ($matcher_name:ident : $t:ty = |$item:ident| $predicate:expr) => {
        pred!($matcher_name<'a> : $t => $t = |$item| $predicate => { $item });
    };
}

#[macro_export]
macro_rules! cases {
    // ident <= ident 
    ($input:ident, $rp:ident, $n:ident <= $matcher:ident, $($rest:tt)*) => {
        let $n = match $matcher($input) {
            Ok(v) => v,
            Err(MatchError::Error(i)) => {
                std::mem::swap(&mut $rp, $input); 
                return Err(MatchError::Error(i));
            },
            Err(MatchError::ErrorEndOfFile) => {
                std::mem::swap(&mut $rp, $input); 
                return Err(MatchError::ErrorEndOfFile);
            },
            Err(MatchError::Fatal(i)) => {
                std::mem::swap(&mut $rp, $input); 
                return Err(MatchError::Fatal(i));
            },
            Err(MatchError::FatalEndOfFile) => {
                std::mem::swap(&mut $rp, $input); 
                return Err(MatchError::FatalEndOfFile);
            },
        };
        cases!($input, $rp, $($rest)*);
    };
    ($input:ident, $rp:ident, $n:ident <= ? $matcher:ident, $($rest:tt)*) => {
        #[allow(unreachable_patterns)]
        let $n = match $matcher($input) {
            Ok(v) => Some(v),
            Err(MatchError::Error(_)) => None,
            Err(MatchError::ErrorEndOfFile) => None,
            Err(MatchError::Fatal(i)) => {
                std::mem::swap(&mut $rp, $input); 
                return Err(MatchError::Fatal(i))
            },
            Err(MatchError::FatalEndOfFile) => {
                std::mem::swap(&mut $rp, $input); 
                return Err(MatchError::FatalEndOfFile);
            },
        };
        cases!($input, $rp, $($rest)*);
    };
    ($input:ident, $rp:ident, $n:ident <= * $matcher:ident, $($rest:tt)*) => {
        let mut ret = vec![];
        loop {
            let mut peek = $input.clone();
            #[allow(unreachable_patterns)]
            match $matcher($input) {
                Ok(v) => ret.push(v),
                Err(MatchError::Error(_)) => {
                    std::mem::swap(&mut peek, $input); 
                    break;
                },
                Err(MatchError::ErrorEndOfFile) => {
                    std::mem::swap(&mut peek, $input); 
                    break;
                },
                Err(MatchError::Fatal(i)) => {
                    std::mem::swap(&mut peek, $input); 
                    return Err(MatchError::Fatal(i));
                },
                Err(MatchError::FatalEndOfFile) => {
                    std::mem::swap(&mut peek, $input); 
                    return Err(MatchError::FatalEndOfFile)
                },
            }

        }
        let $n = ret;
        cases!($input, $rp, $($rest)*);
    };
    ($input:ident, $rp:ident, $n:ident <= ! $matcher:ident, $($rest:tt)*) => {
        #[allow(unreachable_patterns)]
        let $n = match $matcher($input) {
            Ok(v) => v,
            Err(MatchError::Error(i)) => {
                std::mem::swap(&mut $rp, $input); 
                return Err(MatchError::Fatal(i));
            },
            Err(MatchError::ErrorEndOfFile) => {
                std::mem::swap(&mut $rp, $input); 
                return Err(MatchError::FatalEndOfFile);
            },
            Err(MatchError::Fatal(i)) => {
                std::mem::swap(&mut $rp, $input); 
                return Err(MatchError::Fatal(i));
            },
            Err(MatchError::FatalEndOfFile) => {
                std::mem::swap(&mut $rp, $input); 
                return Err(MatchError::FatalEndOfFile);
            },
        };
        cases!($input, $rp, $($rest)*);
    };

    // ident
    ($input:ident, $rp:ident, $matcher:ident, $($rest:tt)*) => {
        cases!($input, $rp, _x <= $matcher, $($rest)*);
    };
    ($input:ident, $rp:ident, ? $matcher:ident, $($rest:tt)*) => {
        cases!($input, $rp, _x <= ? $matcher, $($rest)*);
    };
    ($input:ident, $rp:ident, * $matcher:ident, $($rest:tt)*) => {
        cases!($input, $rp, _x <= * $matcher, $($rest)*);
    };
    ($input:ident, $rp:ident, ! $matcher:ident, $($rest:tt)*) => {
        cases!($input, $rp, _x <= ! $matcher, $($rest)*);
    };

    // ident <= pat
    ($input:ident, $rp:ident, $n:ident <= $p:pat, $($rest:tt)*) => {
        #[allow(unreachable_patterns)]
        let $n = match $input.next() {
            Some((_, item @ $p)) => {
                item
            },
            Some((i, _)) => {
                std::mem::swap(&mut $rp, $input); 
                return Err(MatchError::Error(i)); 
            },
            _ => { 
                std::mem::swap(&mut $rp, $input); 
                return Err(MatchError::ErrorEndOfFile); 
            },
        };
        cases!($input, $rp, $($rest)*);
    };
    ($input:ident, $rp:ident, $n:ident <= ? $p:pat, $($rest:tt)*) => {
        let mut peek = $input.clone();
        #[allow(unreachable_patterns)]
        let $n = match $input.next() {
            Some((_, item @ $p)) => {
                Some(item)
            },
            _ => {
                std::mem::swap(&mut peek, $input); 
                None
            },
        };
        cases!($input, $rp, $($rest)*);
    };
    ($input:ident, $rp:ident, $n:ident <= * $p:pat, $($rest:tt)*) => {
        let mut ret = vec![];
        loop {
            let mut peek = $input.clone();
            #[allow(unreachable_patterns)]
            match $input.next() {
                Some((_, item @ $p)) => {
                    ret.push(item);
                },
                _ => {
                    std::mem::swap(&mut peek, $input); 
                    break;
                },
            }
        }
        let $n = ret;
        cases!($input, $rp, $($rest)*);
    };
    ($input:ident, $rp:ident, $n:ident <= ! $p:pat, $($rest:tt)*) => {
        #[allow(unreachable_patterns)]
        let $n = match $input.next() {
            Some((_, item @ $p)) => {
                item
            },
            Some((i, _)) => {
                std::mem::swap(&mut $rp, $input); 
                return Err(MatchError::Fatal(i)); 
            },
            _ => { 
                std::mem::swap(&mut $rp, $input); 
                return Err(MatchError::FatalEndOfFile); 
            },
        };
        cases!($input, $rp, $($rest)*);
    };
 
    // pat
    ($input:ident, $rp:ident, $p:pat, $($rest:tt)*) => {
        cases!($input, $rp, _x <= $p, $($rest)*);
    };
    ($input:ident, $rp:ident, ? $p:pat, $($rest:tt)*) => {
        cases!($input, $rp, _x <= ? $p, $($rest)*);
    };
    ($input:ident, $rp:ident, * $p:pat, $($rest:tt)*) => {
        cases!($input, $rp, _x <= * $p, $($rest)*);
    };
    ($input:ident, $rp:ident, ! $p:pat, $($rest:tt)*) => {
        cases!($input, $rp, _x <= ! $p, $($rest)*);
    };

    ($input:ident, $rp:ident, $b:block) => {
        return Ok($b);
    };
}

#[macro_export]
macro_rules! seq {
    ($matcher_name:ident<$life:lifetime> : $in_t:ty => $out_t:ty = $($rest:tt)*) => {
        #[allow(dead_code)]
        fn $matcher_name<$life>(input : &mut (impl Iterator<Item = (usize, $in_t)> + Clone)) -> Result<$out_t, MatchError> {
            let mut _rp = input.clone();
            cases!(input, _rp, $($rest)*);
        }
    };

    ($matcher_name:ident<$life:lifetime> : $t:ty = $($rest:tt)*) => {
        seq!($matcher_name<$life> : $t => $t = $($rest)*);
    };

    ($matcher_name:ident : $t:ty = $($rest:tt)*) => {
        seq!($matcher_name<'a> : $t => $t = $($rest)*);
    };

    ($matcher_name:ident : $in_t:ty => $out_t:ty = $($rest:tt)*) => {
        seq!($matcher_name<'a> : $in_t => $out_t = $($rest)*);
    };
}

#[cfg(test)]
mod test { 
    use super::*;

    #[test]
    fn seq_should_reset_input_on_call_failure() -> Result<(), MatchError> {
        seq!(fail: u8 = 0xFF, { 0x00 });
        seq!(main: u8 = 0x00 
                      , fail 
                      , {
            0x00
        });

        let input = vec![0x00, 0x01];
        let mut x = input.into_iter().enumerate();

        let output = main(&mut x);

        assert!( matches!( output, Err(_) ) );

        assert_eq!( x.next(), Some((0, 0x00)) );

        Ok(())
    }

    #[test]
    fn group_with_maybe_should_return_unused_symbol() {
        group!(x: u8 = |input| {
            seq!(a: u8 = ? 0x01, 0x02, { 0x01 });

            a(input)
        });
        let v : Vec<u8> = vec![0x01, 0x03];
        let mut i = v.into_iter().enumerate();

        let o = x(&mut i);
        assert!( matches!( o, Err(MatchError::Error(1))) );

        assert_eq!( i.next(), Some((0, 0x01)) );
    }

    #[test]
    fn alt_with_maybe_should_pass_on_unused_symbol() {
        seq!(a: u8 = ? 0x01, 0x02, { 0x01 });
        seq!(b: u8 = 0x01, 0x03, { 0x02 });
        alt!(main: u8 = a | b);

        let v : Vec<u8> = vec![0x01, 0x03];
        let mut i = v.into_iter().enumerate();

        let o = main(&mut i);
        assert!( matches!( o, Ok(0x02) ) );
    }

    #[test]
    fn alt_with_maybe_should_return_unused_symbol() {
        seq!(a: u8 = ? 0x01, 0x02, { 0x01 });
        alt!(main: u8 = a);

        let v : Vec<u8> = vec![0x01, 0x03];
        let mut i = v.into_iter().enumerate();

        let o = main(&mut i);
        assert!( matches!( o, Err(MatchError::Error(1))) );

        assert_eq!( i.next(), Some((0, 0x01)) );
    }

    #[test]
    fn alt_should_return_unused_symbol() {
        seq!(a: u8 = 0x01, 0x02, { 0x01 });
        alt!(main: u8 = a);

        let v : Vec<u8> = vec![0x01, 0x03];
        let mut i = v.into_iter().enumerate();

        let o = main(&mut i);
        assert!( matches!( o, Err(MatchError::Error(1))) );

        assert_eq!( i.next(), Some((0, 0x01)) );
    }

    #[test]
    fn seq_should_return_unused_symbol() {
        seq!(main: u8 = 0x01, 0x02, { 0x01 });

        let v : Vec<u8> = vec![0x01, 0x03];
        let mut i = v.into_iter().enumerate();

        let o = main(&mut i);
        assert!( matches!( o, Err(MatchError::Error(1))) );

        assert_eq!( i.next(), Some((0, 0x01)) );
    }

    #[test]
    fn seq_with_maybe_should_return_unused_symbol() {
        seq!(main: u8 = ? 0x01, 0x02, { 0x01 });

        let v : Vec<u8> = vec![0x01, 0x03];
        let mut i = v.into_iter().enumerate();

        let o = main(&mut i);
        assert!( matches!( o, Err(MatchError::Error(1))) );

        assert_eq!( i.next(), Some((0, 0x01)) );
    }

    #[test]
    fn group_should_match() -> Result<(), MatchError> {
        group!(main: u8 = |input| {
            seq!(a: u8 = x <= _, y <= 0x01, { x + y });
            
            a(input)
        });

        let v : Vec<u8> = vec![0x05, 0x01];
        let mut i = v.into_iter().enumerate();

        let o = main(&mut i)?;

        assert_eq!( o, 0x06 );

        Ok(())
    }

    #[test]
    fn group_should_handle_lifetime() -> Result<(), MatchError> {
        struct Input(u8);

        group!(main<'a>: &'a Input = |input| {
            seq!(a<'a>: &'a Input = _, y <= Input(0x01), { y });
            
            a(input)
        });

        let v : Vec<Input> = vec![Input(0x05), Input(0x01)];
        let mut i = v.iter().enumerate();

        let o = main(&mut i)?;

        assert_eq!( o.0, 0x01 );

        Ok(())
    }

    #[test]
    fn group_should_handle_different_output_type() -> Result<(), MatchError> {
        struct Output(u8);

        group!(main: u8 => Output = |input| {
            seq!(a: u8 => Output = x <= _, y <= 0x01, { Output(x + y) });
            
            a(input)
        });

        let v : Vec<u8> = vec![0x05, 0x01];
        let mut i = v.into_iter().enumerate();

        let o = main(&mut i)?;

        assert_eq!( o.0, 0x06 );

        Ok(())
    }

    #[test]
    fn group_should_handle_different_output_type_with_lifetime() -> Result<(), MatchError> {
        struct Input(u8);
        struct Output<'a>(&'a Input);

        group!(main<'a>: &'a Input => Output<'a> = |input| {
            seq!(a<'a>: &'a Input => Output<'a> = _, y <= Input(0x01), { Output(y) });
            
            a(input)
        });

        let v : Vec<Input> = vec![Input(0x05), Input(0x01)];
        let mut i = v.iter().enumerate();

        let o = main(&mut i)?;

        assert_eq!( o.0.0, 0x01 );

        Ok(())
    }

    #[test]
    fn seq_should_handle_lifetime() -> Result<(), MatchError> {
        struct Input(u8);

        seq!(main<'a>: &'a Input = a <= Input(0x00), { a });

        let v : Vec<Input> = vec![Input(0x00)];
        let mut i = v.iter().enumerate();

        let o = main(&mut i)?;

        assert_eq!( o.0, 0x00 );
        Ok(())
    }

    #[test]
    fn seq_should_handle_different_output_type() -> Result<(), MatchError> {
        struct Output(u8);

        seq!(main: u8 => Output = a <= 0x00, { Output(a) });

        let v : Vec<u8> = vec![0x00];
        let mut i = v.into_iter().enumerate();

        let o = main(&mut i)?;

        assert_eq!( o.0, 0x00 );
        Ok(())
    }

    #[test]
    fn seq_should_handle_different_output_type_with_lifetime() -> Result<(), MatchError> {
        struct Input(u8);
        struct Output<'a>(&'a Input);

        seq!(main<'a>: &'a Input => Output<'a> = a <= Input(0x00), { Output(a) });

        let v : Vec<Input> = vec![Input(0x00)];
        let mut i = v.iter().enumerate();

        let o = main(&mut i)?;

        assert_eq!( o.0.0, 0x00 );
        Ok(())
    }

    #[test]
    fn seq_should_handle_anon_fatal_pattern() {
        seq!(main: u8 = ! 0x00, { 0xFF });

        let v : Vec<u8> = vec![0x01];
        let mut i = v.into_iter().enumerate();

        let o = main(&mut i);

        assert!( matches!( o, Err(MatchError::Fatal(_) ) ) );
    }

    #[test]
    fn seq_should_handle_fatal_pattern() {
        seq!(main: u8 = x <= ! 0x00, { x });

        let v : Vec<u8> = vec![0x01];
        let mut i = v.into_iter().enumerate();

        let o = main(&mut i);

        assert!( matches!( o, Err(MatchError::Fatal(_) ) ) );
    }

    #[test]
    fn seq_should_handle_anon_fatal_call() {
        seq!(item: u8 = a <= 0x00, { a });
        seq!(main: u8 = ! item, { 0xFF });

        let v : Vec<u8> = vec![0x01];
        let mut i = v.into_iter().enumerate();

        let o = main(&mut i);

        assert!( matches!( o, Err(MatchError::Fatal(_) ) ) );
    }

    #[test]
    fn seq_should_handle_fatal_call() {
        seq!(item: u8 = a <= 0x00, { a });
        seq!(main: u8 = a <= ! item, { a });

        let v : Vec<u8> = vec![0x01];
        let mut i = v.into_iter().enumerate();

        let o = main(&mut i);

        assert!( matches!( o, Err(MatchError::Fatal(_) ) ) );
    }

    #[test]
    fn seq_should_handle_named_call() -> Result<(), MatchError> {
        seq!(item: u8 = a <= _, { a });
        seq!(main: u8 = a <= item, b <= item, { a + b });

        let v : Vec<u8> = vec![0x01, 0x02];
        let mut i = v.into_iter().enumerate();

        let o = main(&mut i)?;

        assert_eq!( o, 3 );

        Ok(())
    }

    #[test]
    fn seq_should_handle_maybe_named_call() -> Result<(), MatchError> {
        seq!(item: u8 = a <= _, { a });
        seq!(main: u8 = a <= ? item, b <= ? item, { a.unwrap() + b.unwrap() });

        let v : Vec<u8> = vec![0x01, 0x02];
        let mut i = v.into_iter().enumerate();

        let o = main(&mut i)?;

        assert_eq!( o, 3 );

        Ok(())
    }

    #[test]
    fn seq_should_handle_zero_or_more_named_call() -> Result<(), MatchError> {
        seq!(one: u8 = a <= 0x01, { a });
        seq!(two: u8 = a <= 0x02, { a });
        seq!(three: u8 = a <= 0x03, { a });
        seq!(main: u8 = a <= * one, b <= * two, c <= * three, {
            let x = a.into_iter().fold(0, |acc, v| acc + v);
            let y = b.into_iter().fold(x, |acc, v| acc + v);
            c.into_iter().fold(y, |acc, v| acc + v)
        });

        let v : Vec<u8> = vec![0x01, 0x01, 0x01, 0x02, 0x02];
        let mut i = v.into_iter().enumerate();

        let o = main(&mut i)?;

        assert_eq!( o, 7 );

        Ok(())
    }

    #[test]
    fn seq_should_handle_anon_call() -> Result<(), MatchError> {
        seq!(item: u8 = a <= 0xFF, { a });
        seq!(main: u8 = item, item, { 0xFF });

        let v : Vec<u8> = vec![0xFF, 0xFF];
        let mut i = v.into_iter().enumerate();

        let o = main(&mut i)?;

        assert_eq!( o, 0xFF );

        Ok(())
    }

    #[test]
    fn seq_should_handle_maybe_anon_call() -> Result<(), MatchError> {
        seq!(item: u8 = a <= 0xFF, { a });
        seq!(main: u8 = ? item, ? item, { 0xFF });

        let v : Vec<u8> = vec![0xFF, 0xFF];
        let mut i = v.into_iter().enumerate();

        let o = main(&mut i)?;

        assert_eq!( o, 0xFF );

        Ok(())
    }

    #[test]
    fn seq_should_handle_zero_or_more_anon_call() -> Result<(), MatchError> {
        seq!(one: u8 = a <= 0x01, { a });
        seq!(two: u8 = a <= 0x02, { a });
        seq!(three: u8 = a <= 0x03, { a });
        seq!(main: u8 = * one, * two, * three, { 0xFF });

        let v : Vec<u8> = vec![0x01, 0x01, 0x01, 0x02, 0x02];
        let mut i = v.into_iter().enumerate();

        let o = main(&mut i)?;

        assert_eq!( o, 0xFF );

        Ok(())
    }


    #[test]
    fn seq_should_handle_zero_or_more_anon_pattern() -> Result<(), MatchError> {
        seq!(main: u8 = * 0x01, * 0x03, * 0x02, { 0xFF });

        let v : Vec<u8> = vec![0x01, 0x01, 0x01, 0x02, 0x02];
        let mut i = v.into_iter().enumerate();

        let o = main(&mut i)?;

        assert_eq!( o, 0xFF );
        assert!( matches!( i.next(), None ));

        Ok(())
    }

    #[test]
    fn seq_should_handle_zero_or_more_named_pattern() -> Result<(), MatchError> {
        seq!(main: u8 = a <= * 0x01, b <= * 0x03, c <= * 0x02, {
            let x = a.into_iter().fold(0, |acc, v| acc + v);
            let y = b.into_iter().fold(x, |acc, v| acc + v);
            c.into_iter().fold(y, |acc, v| acc + v)
        });

        let v : Vec<u8> = vec![0x01, 0x01, 0x01, 0x02, 0x02];
        let mut i = v.into_iter().enumerate();

        let o = main(&mut i)?;

        assert_eq!( o, 7 );

        Ok(())
    }
    
    #[test]
    fn seq_should_handle_multiple_maybe_patterns() -> Result<(), MatchError> {
        seq!(main: u8 = a <= ? 0x01, b <= ? 0x02, { 
            a.unwrap() + b.unwrap()
        });

        let v : Vec<u8> = vec![0x01, 0x02];
        let mut i = v.into_iter().enumerate();

        let o = main(&mut i)?;

        assert_eq!( o, 3 );

        Ok(())
    }

    #[test]
    fn seq_should_handle_named_patterns() -> Result<(), MatchError> {
        seq!(main: u8 = a <= 0x01, b <= 0x02, { a + b });

        let v : Vec<u8> = vec![0x01, 0x02];
        let mut i = v.into_iter().enumerate();

        let o = main(&mut i)?;

        assert_eq!( o, 3 );

        Ok(())
    }

    #[test]
    fn seq_should_handle_maybe_named_patterns_thats_present() -> Result<(), MatchError> {
        seq!(main: u8 = _a <= ? 0x01, b <= _, { b });

        let v : Vec<u8> = vec![0xFF, 0x02];
        let mut i = v.into_iter().enumerate();

        let o = main(&mut i)?;

        assert_eq!( o, 0xFF );

        Ok(())
    }

    #[test]
    fn seq_should_handle_anon_patterns() -> Result<(), MatchError> {
        seq!(main: u8 = 0x01, 0x02, { 0xFF });

        let v : Vec<u8> = vec![0x01, 0x02];
        let mut i = v.into_iter().enumerate();

        let o = main(&mut i)?;

        assert_eq!( o, 0xFF );

        Ok(())
    }

    #[test]
    fn seq_should_handle_maybe_anon_patterns_thats_present() -> Result<(), MatchError> {
        seq!(main: u8 = ? 0x01, _, { 0xEE });

        let v : Vec<u8> = vec![0xFF, 0x02];
        let mut i = v.into_iter().enumerate();

        let o = main(&mut i)?;

        assert_eq!( o, 0xEE );

        Ok(())
    }

    #[test]
    fn alt_should_handle_block() -> Result<(), MatchError> {
        pred!(even : u8 = |x| x % 2 == 0);
        pred!(odd : u8 = |x| x % 2 == 1);
        alt!(even_or_odd : u8 = even | odd => |b| { b + 1 });

        let v : Vec<u8> = vec![3, 3];
        let mut i = v.into_iter().enumerate();

        let o = even_or_odd(&mut i)?;

        assert_eq!( o, 4 );

        Ok(())
    }

    #[test]
    fn alt_should_handle_lifetime_with_block() -> Result<(), MatchError> {
        struct Input(u8);
        
        pred!(even<'a> : &'a Input = |x| x.0 % 2 == 0);
        pred!(odd<'a> : &'a Input = |x| x.0 % 2 == 1);
        alt!(even_or_odd<'a> : &'a Input = even | odd => |b| { 
            b
        });

        let v : Vec<Input> = vec![Input(3), Input(3)];
        let mut i = v.iter().enumerate();

        let o = even_or_odd(&mut i)?;

        assert_eq!( o.0, 3 );

        Ok(())
    }

    #[test]
    fn alt_should_handle_different_output_type_with_block() -> Result<(), MatchError> {
        struct Output(u8);
        
        pred!(even : u8 => Output = |x| x % 2 == 0 => { Output(x) });
        pred!(odd : u8 => Output = |x| x % 2 == 1 => { Output(x) });
        alt!(even_or_odd : u8 => Output = even | odd => |b| { b });

        let v : Vec<u8> = vec![3, 3];
        let mut i = v.into_iter().enumerate();

        let o = even_or_odd(&mut i)?;

        assert_eq!( o.0, 3 );

        Ok(())
    }
    
    #[test]
    fn alt_should_handle_different_output_type_with_lifetime_block() -> Result<(), MatchError> {
        struct Input(u8);
        struct Output<'a>(&'a Input);
        
        pred!(even<'a> : &'a Input => Output<'a> = |x| x.0 % 2 == 0 => { Output(x) });
        pred!(odd<'a> : &'a Input => Output<'a> = |x| x.0 % 2 == 1 => { Output(x) });
        alt!(even_or_odd<'a> : &'a Input => Output<'a> = even | odd => |b| { b });

        let v : Vec<Input> = vec![Input(3), Input(3)];
        let mut i = v.iter().enumerate();

        let o = even_or_odd(&mut i)?;

        assert_eq!( o.0.0, 3 );

        Ok(())
    }

    #[test]
    fn alt_should_match() -> Result<(), MatchError> {
        pred!(even : u8 = |x| x % 2 == 0);
        pred!(odd : u8 = |x| x % 2 == 1);
        alt!(even_or_odd : u8 = even | odd);

        let v : Vec<u8> = vec![3, 3];
        let mut i = v.into_iter().enumerate();

        let o = even_or_odd(&mut i)?;

        assert_eq!( o, 3 );

        Ok(())
    }

    #[test]
    fn alt_should_not_match() {
        pred!(even : u8 = |x| x % 2 == 0);
        pred!(five : u8 = |x| x == 5);
        alt!(even_or_five : u8 = even | five);

        let v : Vec<u8> = vec![3, 3];
        let mut i = v.into_iter().enumerate();

        let o = even_or_five(&mut i);

        assert!( matches!(o, Err(MatchError::Error(_))) );
    }

    #[test]
    fn alt_should_handle_lifetime() -> Result<(), MatchError> {
        struct Input(u8);
        
        pred!(even<'a> : &'a Input = |x| x.0 % 2 == 0);
        pred!(odd<'a> : &'a Input = |x| x.0 % 2 == 1);
        alt!(even_or_odd<'a> : &'a Input = even | odd);

        let v : Vec<Input> = vec![Input(3), Input(3)];
        let mut i = v.iter().enumerate();

        let o = even_or_odd(&mut i)?;

        assert_eq!( o.0, 3 );

        Ok(())
    }

    #[test]
    fn alt_should_handle_different_output_type() -> Result<(), MatchError> {
        struct Output(u8);
        
        pred!(even : u8 => Output = |x| x % 2 == 0 => { Output(x) });
        pred!(odd : u8 => Output = |x| x % 2 == 1 => { Output(x) });
        alt!(even_or_odd : u8 => Output = even | odd);

        let v : Vec<u8> = vec![3, 3];
        let mut i = v.into_iter().enumerate();

        let o = even_or_odd(&mut i)?;

        assert_eq!( o.0, 3 );

        Ok(())
    }
    
    #[test]
    fn alt_should_handle_different_output_type_with_lifetime() -> Result<(), MatchError> {
        struct Input(u8);
        struct Output<'a>(&'a Input);
        
        pred!(even<'a> : &'a Input => Output<'a> = |x| x.0 % 2 == 0 => { Output(x) });
        pred!(odd<'a> : &'a Input => Output<'a> = |x| x.0 % 2 == 1 => { Output(x) });
        alt!(even_or_odd<'a> : &'a Input => Output<'a> = even | odd);

        let v : Vec<Input> = vec![Input(3), Input(3)];
        let mut i = v.iter().enumerate();

        let o = even_or_odd(&mut i)?;

        assert_eq!( o.0.0, 3 );

        Ok(())
    }

    #[test]
    fn pred_should_match() -> Result<(), MatchError> {
        pred!(even : u8 = |x| x % 2 == 0);

        let v : Vec<u8> = vec![2, 3];
        let mut i = v.into_iter().enumerate();

        let o = even(&mut i)?;

        assert_eq!( o, 2 );

        Ok(())
    }

    #[test]
    fn pred_should_not_match() {
        pred!(even : u8 = |x| x % 2 == 0);

        let v : Vec<u8> = vec![3, 2];
        let mut i = v.into_iter().enumerate();

        let o = even(&mut i);

        assert!( matches!( o, Err(MatchError::Error(_)) ) );
    }

    #[test]
    fn pred_should_handle_lifetime() -> Result<(), MatchError> {
        struct Input(u8);
        
        pred!(even<'a> : &'a Input = |x| x.0 % 2 == 0);

        let v : Vec<Input> = vec![Input(2), Input(3)];
        let mut i = v.iter().enumerate();

        let o = even(&mut i)?;

        assert_eq!( o.0, 2 );

        Ok(())
    }

    #[test]
    fn pred_should_handle_output_block() -> Result<(), MatchError> {
        struct Output(u8);

        pred!(even : u8 => Output = |x| x % 2 == 0 => { Output(x + 1) });

        let v : Vec<u8> = vec![2, 3];
        let mut i = v.into_iter().enumerate();

        let o = even(&mut i)?;

        assert_eq!( o.0, 3 );

        Ok(())
    }

    #[test]
    fn pred_should_handle_output_block_with_lifetime() -> Result<(), MatchError> {
        struct Input(u8);
        struct Output<'a>(&'a Input);

        pred!(even<'a> : &'a Input => Output<'a> = |x| x.0 % 2 == 0 => { Output(x) });

        let v : Vec<Input> = vec![Input(2), Input(3)];
        let mut i = v.iter().enumerate();

        let o = even(&mut i)?;

        assert_eq!( o.0.0, 2 );

        Ok(())
    }
}