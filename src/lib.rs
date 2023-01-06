
//! # Birgitte_fibonacci
//!
//! `birgitte_fibonacci` has functions that calculate the 
//! fibonacci number of a given number.

use std::hash::Hash;
use std::{collections::HashMap};
use std::ops::{Add, Sub};
use memoize::memoize;


pub trait Int: Add<Output=Self> + Sub<Output=Self> + PartialEq + Copy {
    fn zero() -> Self;
    fn one() -> Self;
}

impl Int for usize {
    fn zero() -> Self { 0 }
    fn one() -> Self { 1 }
}

impl Int for u128 {
    fn zero() -> Self { 0 }
    fn one() -> Self { 1 }
}

impl Int for u64 {
    fn zero() -> Self { 0 }
    fn one() -> Self { 1 }
}

impl Int for u32 {
    fn zero() -> Self { 0 }
    fn one() -> Self { 1 }
}

impl Int for u16 {
    fn zero() -> Self { 0 }
    fn one() -> Self { 1 }
}

impl Int for u8 {
    fn zero() -> Self { 0 }
    fn one() -> Self { 1 }
}

/// Caclculates fibonacci with custom memoization
/// Supports: u8, u16, u32, u64, u128, usize
/// 
/// # Example
/// 
///  assert_eq!(fib::<usize>(30), 832040);
/// 
/// # Panic
/// 
/// If the number that is created is to big for the datastructure
pub fn fib<T: Int + Hash + Eq>(n: T) -> T{

    fn fib_cache<T: Int + Hash + Eq> (cache: &mut HashMap<T,T>, n: T) -> T {
        match cache.get(&n).map(|entry| entry.clone()){
            Some(value) => value,
            None => {
               let value =  match n {
                    number if number == T::zero() => T::zero(),
                    number if number == T::one() => T::one(),
                    _ => fib_cache(cache, n-T::one()) + fib_cache(cache, n-T::one()-T::one())
                };
                cache.insert(n, value);
                return value;
            }
        }
    }

    let mut cache: HashMap<T,T> = HashMap::new();
    fib_cache(&mut cache, n)
}

/// Caclculates fibonacci with memoizate
/// Supports: usize
/// 
/// # Example
/// 
///  assert_eq!(fib_memo(30), 832040);
/// 
/// # Panic
/// 
/// If the number that is created is to big for the datastructure
pub fn fib_memo(n: usize) -> usize {

    #[memoize] //Not to expose the functions created by memoize
    fn memo(n: usize) -> usize{
       match n  {
            0 => 0,
            1 => 1,
            _ => fib(n-1) + fib(n-2)
        }     
    }
    
    memo(n)
}

#[cfg(test)]
mod test_fib{
    use crate::fib;
    use crate::fib_memo;

    #[test]
    fn fib_works(){
       assert_eq!(fib::<usize>(2), 1);
       assert_eq!(fib::<usize>(6), 8);
       assert_eq!(fib::<usize>(15), 610);
       assert_eq!(fib::<usize>(30), 832040);
       assert_eq!(fib::<u128>(100), 354224848179261915075);
    }

    #[test]
    fn fib_memo_works(){
       assert_eq!(fib_memo(2), 1);
       assert_eq!(fib_memo(6), 8);
       assert_eq!(fib_memo(15), 610);
       assert_eq!(fib_memo(30), 832040);
       assert_eq!(fib_memo(50), 12586269025);
    }

}
