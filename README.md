Simple matching of one char or byte, similar to regex

Lightweight and easy to use, and can work conveniently on `u8` and `Option`


# Examples

```rust
use char_classes::any;

assert!(any("ab",       'a'));
assert!(any("ab",       'b'));
assert!(any("a-c",      'a'));
assert!(any("a-c",      'b'));
assert!(any("a-ce-f",   'e'));
assert!(any("a-ce-",    '-'));
assert!(any("a-ce-",    'e'));
assert!(any("a-c",      Some('b')));
assert!(any("a-c",      ['b', 'd']));
assert!(any("a-c",      "bd"));

assert!(! any("a-c",    '-'));
assert!(! any("a-ce-",  'f'));

assert!(! any("a-c",    None::<char>));
assert!(! any("a-c",    ['d', 'b']));
assert!(! any("a-c",    "db"));
```

**Match byte**:

```rust
use char_classes::any;

assert!(any(b"ab",      b'a'));
assert!(any(b"ab",      b'b'));
assert!(any(b"ab",      b"bd"));

assert!(! any(b"ab",     b'c'));
assert!(! any(b"ab",     b"db"));
```

**Using macros for better performance**:

```rust
use char_classes::any;

assert!(any!(b"ab",      b'a'));
assert!(any!(b"ab",      b'b'));
assert!(any!(b"ab",      b"bd"));

assert!(any!(^b"ab",     b'c'));
assert!(any!(^b"ab",     b"db"));
```
