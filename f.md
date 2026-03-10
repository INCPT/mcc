# General

The language is white space sensitive. Nested blocks are intended by two spaces. No semicolons at the end of lines.

# Comments

Comments are C++ style: // and /* */

# Bindings

Bindings must always have a type and be initialized with a value:

```
a: type = value
```

# Primitive types: i32, i64, f32, f64, bool

```
a: i32 = 0
b: f32 = 0.0
c: bool = true // or false
```

# Assignment

```
a = 1
b = 2.0
a++
b *= 10.0
```

++, *=, /=, -=, += are also supported.

# Unary negation

```
a = -5
```

# Boolean negation

```
a: bool = !false
```

# Binary operations/relations

+, -, /, *, ^, %, <, <=, >, >=, !=, ==

# Arrays: i32[8], f64[128]

Arrays must always have a size.

```
c: i32[8] = [0...] // initialize with 0s
d: i32[128] = [1.0...] // initialize with 1.0s
```

# Structures

```
f: { x: f32, y: i64[8] } = { x: 0.0, y: [0...] }
g: {
  x: f32 // if multiline commas can be ommited
  y: i64[8]
} = {
  x: 0.0
  y: [0...]
}
```

# Functions

```
f: f32 -> f32 = \a -> a + 1 // types and lambdas are Haskell style
g: { a: f32, b: i32 } -> { x: f32[8] } = \o -> { x: [0.0....] } // functions accept all types
g: { a: f32, b: i32 } -> { x: f32[8] } = \props ->
  // functions can be multiline
  j: f32 = 0
  p: in32 = 0

  return j + p // function might end with return statement

h: f32 -> f32 -> f32 = \a b -> a + b // or \a -> \b -> a + b

x: f32 = h 0.0 1.0 // functions are called Haskell style, with spaces between the arguments
y: { x: f32[8] } = g { a: 0.0, b: 0 }
z: f32 -> f32 = h 5.0 // functions are curried by default
```

# Splices

```
g: { a: f32, b: i32 } -> { x: f32[8] } = \{..} -> ... // a structure argument can be spliced into the environment, e.g. now both `a` and `b` are in scope
{..}: { x: i32, y: i32 } = ... // x and y are now in scope
```

# Type aliases

```
type in = f32[128]
type out = { x: f32[8], y: f32[8] }
type compute = in -> out
```

# Parenthesis

Can be placed around any expression, but not statements.

```
a: i32 = (1 + 2)
b: bool = (1 + 2) > 3
f: f32 -> f32 = (\a -> a)
```

# Math

All standard C math functions are available in both 32 and 64 variants:

```
a: f32 = sin32 0.1
b: f64 = sin64 0.1
```

# While loops

```
while a == true
  a = false
  i++
```

# For loops

```
for i: i32 = 0; i < 100; i++
  table[i] = i
```

# Switch statements

```
  switch i
    0 ->
      p = 0
    1 ->
      q = 0
    _ ->
      p = 1
      q = 1
```

# Recursion

Recursion (self and mutual) is disallowed.
