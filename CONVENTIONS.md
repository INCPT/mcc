- Always prefer the Semigroup operator <> over the List ++ where possible

- Use list comprehensions where possible

-- Prefer `[ (f a, b) | (a, b) <- zip as bs ]` over `zipWith (\(a, b) -> (f a, b)) as bs`
-- However, use a function when currying is possible: prefer `f = fmap g` over `f as = [ g a | a <- as ]`

- Use let bindings only if they make the code much clearer:
    Prefer
    ```
    pure (f a)
    ```

    over

    ```
    let thing = f a
    pure thing
    ```

- Prefer `where` over `let`

- Prefer `mconcat` over a multiline bracketed `<>` expression:
  ```
  mconcat
    [ longline1
    , lineline2
    ]
  ```

  over
  ```
  (longline1 <>
  longline2)
  ```

  Single line `(a <> b)` expressions are fine.
