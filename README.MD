# Birgitte fibonacci

`birgitte_fibonacci` has functions that calculate the  fibonacci number of a given number.

## Examples

### `fib`
Caclculates fibonacci with custom memoization

Supports: u8, u16, u32, u64, u128, usize

```assert_eq!(fib::<usize>(30), 832040);```

### `fib_memo`
Caclculates fibonacci with memoizate

Supports: usize

```assert_eq!(fib_memo(30), 832040);```

## Panic

If the number that is created is to big for the datastructure