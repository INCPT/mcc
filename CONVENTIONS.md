- Use `pure` over `return`

- Always prefer the Semigroup operator <> over the List ++ where possible

- Use `traverse` over `mapM`, `traverse_` over `mapM_`

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

- Prefer `where` over `let` (but this obviously doesn't work in `do` blocks)

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

- Indent the `then` and `else` clauses of an `if` expression:
    ```
    if condition
      then ...
      else ...
    ```

- Put empty lines between loosely similar groups of lines (but try to not have too many singe line groups):
    ```
      op <- elements [Add, Sub, Mul, Mod, And, Or, Xor, Min, Max]

      let ctx' = ctx { maxDepth = maxDepth ctx - 1 }

      a <- scale (`div` 2) $ genExprOfType ctx' t
      b <- scale (`div` 2) $ genExprOfType ctx' t

      pure $ EOp t op a b
    ```

    ```
      genFuncType = do
        numParams <- choose (0, 3)
        params <- replicateM numParams (genType (depth - 1))
        retType <- genType (depth - 1)

        pure $ TAbs params retType
    ```