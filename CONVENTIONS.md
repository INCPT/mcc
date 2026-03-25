- Always prefer <> over ++

- Use list comprehensions where possible

-- Prefer `[ (f a, b) | (a, b) <- zip as bs ]` over `zipWith (\(a, b) -> (f a, b)) as bs`

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