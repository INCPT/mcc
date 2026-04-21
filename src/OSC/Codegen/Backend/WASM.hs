module OSC.Codegen.Backend.WASM where

{-

In WebAssembly, a "statically known" array is implemented by reserving a specific offset in Linear Memory. You then use i32.load and i32.store to read and write to that address. 
Here is a WAT (WebAssembly Text) example showing how to reserve an array of 10 integers starting at memory address 0, along with functions to get and set values.

(module
  ;; 1. Define memory. 1 page = 64KB.
  (memory (export "memory") 1)

  ;; 2. Optional: Pre-initialize the array with data at address 0
  ;; This puts [10, 20, 30] at the start of memory.
  (data (i32.const 0) "\0a\00\00\00\14\00\00\00\1e\00\00\00")

  ;; Function to SET a value: array[index] = value
  ;; The array starts at offset 0. Each i32 is 4 bytes.
  (func (export "set_array_val") (param $index i32) (param $value i32)
    ;; Calculate address: index * 4
    local.get $index
    i32.const 4
    i32.mul
    ;; Push value to store
    local.get $value
    ;; Store the value at (index * 4)
    i32.store
  )

  ;; Function to GET a value: return array[index]
  (func (export "get_array_val") (param $index i32) (result i32)
    ;; Calculate address: index * 4
    local.get $index
    i32.const 4
    i32.mul
    ;; Load from memory at that address
    i32.load
  )
)

Key Technical Details

    Addressing: Since memory is a byte array, you must multiply the index by the size of your type (4 bytes for i32, 8 for f64) to find the correct address. 
    Static Reservation: In a real project, you manually track which addresses are "reserved" for your static arrays. For example, if Array A is at 0-40, you might start Array B at address 44.
    Initialization: The (data ...) section allows you to bake initial values directly into the binary, which are loaded into memory when the module instantiates. 
    Security: Wasm checks bounds automatically. If you try to access an address beyond your allocated memory pages, it will trap (crash).

---

Using the offset parameter is the standard way to handle multiple static arrays without an allocator. You effectively partition your linear memory into fixed blocks.
Memory Layout Example
Imagine you want two static arrays:

    Array A: 10 integers (40 bytes), starting at address 0.
    Array B: 5 integers (20 bytes), starting at address 100. 

In WebAssembly, you don't "declare" these as separate objects; you simply use the immediate offset to target the correct starting point.

(module
  (memory (export "memory") 1)

  ;; --- ARRAY A (Starts at address 0) ---
  (func (export "set_A") (param $index i32) (param $val i32)
    local.get $index
    i32.const 4
    i32.mul
    local.get $val
    ;; No offset needed (or offset=0)
    i32.store 
  )

  ;; --- ARRAY B (Starts at address 100) ---
  (func (export "set_B") (param $index i32) (param $val i32)
    local.get $index
    i32.const 4
    i32.mul
    local.get $val
    ;; Static offset adds 100 to whatever index*4 is on the stack
    i32.store offset=100
  )

  ;; --- ARRAY B CONSTANT ACCESS ---
  ;; Accessing Array B's 3rd element (index 2) directly
  (func (export "get_B_const") (result i32)
    i32.const 0
    ;; Effective address = 0 + 100 (base) + 8 (index 2 * 4 bytes)
    i32.load offset=108 
  )
)

Why this is powerful

    Zero Runtime Cost: The engine adds the offset to the base address during the memory cycle. It's "free" math compared to doing an i32.add in code. 
    Virtual Structs: This is how C/Rust compilers handle structs. A "pointer" to a struct is pushed to the stack, and every field access uses i32.load offset=N where N is the field's position inside that struct. 
    Static Safety: By using a static offset for your "Base Address" and keeping your indices within bounds, you prevent your arrays from overlapping. 

Best Practices for Multiple Arrays

    Alignment: Try to align your starting offsets to 4 or 8 bytes. Wasm can handle unaligned loads, but they are often slower on some hardware. 
    Data Sections: Use the (data ...) section to pre-fill these specific regions.

(data (i32.const 0) "\01\02\03")   ;; Initial values for Array A
(data (i32.const 100) "\09\08\07") ;; Initial values for Array B

Shadow Stack: In complex modules, it is common to reserve the first few kilobytes for static data (like these arrays) and start your dynamic "heap" at a higher GLOBAL_BASE address (e.g., 1024). 

--- SELECTION

In WebAssembly (Wasm), you can achieve "goto" functionality using the br_table instruction, which acts as a jump table or a "computed jump". This is the standard way to implement switch statements or dispatch logic in Wasm. 
Implementation Methods

    Method 1: Array Lookup (Compute-All)
    Pre-calculate all possible results, store them in linear memory, and use a load instruction with the index.
    Method 2: Binary Search (If-Tree)
    Use a tree of if/else instructions to narrow down the index in
    time. This is often faster for small sets because it avoids memory access entirely. 
    Method 3: br_table (Wasm's "Goto")
    Load the index onto the stack and use br_table. It jumps to a specific label based on the index value, allowing you to execute only the relevant pure computation.


The Final Heuristic Formula

(Total cost of all computations + one memory load)
(Cost of logarithmic branches + one computation)
(Cost of a jump table lookup + one computation)

The following example shows how to calculate the -th element of [a, b, c] where a, b, c are results of pure computations.

(func $lookup_expression (param $i i32) (result i32)
  ;; Outer block to catch the result of the selected computation
  (block $exit (result i32)
    ;; Each nested block represents a "case" in the jump table
    (block $case_c
      (block $case_b
        (block $case_a
          ;; Load the index and jump. 
          ;; If $i=0, jumps to $case_a. If $i=1, jumps to $case_b.
          ;; If $i=2, jumps to $case_c. If $i > 2, it hits the 'default' (last label).
          local.get $i
          br_table $case_a $case_b $case_c $case_c
        )
        ;; Computation 'a' (e.g., 10 + 5)
        i32.const 15
        br $exit
      )
      ;; Computation 'b' (e.g., 20 * 2)
      i32.const 40
      br $exit
    )
    ;; Computation 'c' (e.g., 100 / 4)
    i32.const 25
  )
)

The Jump: When the index is provided, br_table pops it and jumps to the end of the corresponding block.
Selective Execution: Because the jump skips everything before the target block's end marker, only the code following that specific block is executed. The br $exit at the end of each "case" ensures the other computations are skipped once yours is done.

-}

data Config = Config
  { smallArrayMaxLength :: Int -- | Small arrays are returned on the stack
  }

{-
  where
    needsStackMap :: Map FuncRef Bool
    needsStackMap = fmap funcNeedsStack dfm.funcMap
      where
        funcNeedsStack (C.LamAnn typ _ bindings body) = or
          [ C.sizeOfType typ > cfg.smallArrayMaxLength
          , or [ M.findWithDefault False fr needsStackMap | Func fr <- universe body ]
          , or [ M.findWithDefault False fr needsStackMap | (_, _, bbody) <- bindings, Func fr <- universe bbody ]
          ]
-}