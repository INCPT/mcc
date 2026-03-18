Great questions! Let me address both:

## 1. Passing Return Buffer as Argument

This technique is called **"return value optimization via out-parameters"** or more specifically:

- **"Destination-passing style"** (DPS)
- **"Out-parameter passing"**
- **"Caller-allocated return"**

In compiler literature, this is often part of **"struct return optimization"** or **"aggregate return optimization"**.

In languages like C, this is done manually with out-parameters. In compilers, this is often called **"NRVO" (Named Return Value Optimization)** when the compiler automatically transforms code to write directly to the caller's destination.

## 2. Slice Forwarding / Copy Elimination

The technique of mapping argument slices directly to return value slices to eliminate copies is called:

- **"Copy propagation"** (when combined with dataflow analysis)
- **"Alias analysis"** (understanding when two references point to the same memory)
- **"Forwarding"** or **"slice forwarding"**
- **"Destination propagation"** (propagating the destination buffer through the call chain)

More specifically, what you're describing is a form of:
- **"Deforestation"** - eliminating intermediate data structures
- **"Fusion"** - combining operations to avoid materialization
- **"View/slice optimization"** - recognizing that slices don't need copying

## Algorithms & Libraries

### Relevant Algorithms:

1. **Alias Analysis**
   - Points-to analysis
   - Shape analysis
   - Region-based memory management

2. **Dataflow Analysis**
   - Reaching definitions
   - Available expressions
   - Live variable analysis

3. **Deforestation/Fusion**
   - Stream fusion (used in Haskell's `vector` library)
   - Shortcut fusion (foldr/build fusion)

### Haskell Libraries:

1. **`llvm-hs`** - LLVM bindings; LLVM has sophisticated alias analysis
   - `llvm-hs-pure` for pure IR construction
   - LLVM's `AliasAnalysis` and `MemoryDependenceAnalysis` passes

2. **`hoopl`** - Dataflow optimization framework
   - Good for implementing custom dataflow analyses
   - Can track slice/buffer relationships

3. **`compdata`** - Compositional data types
   - For building ASTs with annotations
   - Can annotate nodes with slice/buffer information

4. **`recursion-schemes`** - For traversing and transforming ASTs
   - Useful for propagating destination information through the tree

5. **`fgl`** (Functional Graph Library)
   - For building control flow graphs
   - Useful for interprocedural analysis

### Specific Techniques:

For your use case, you'd want to implement:

```haskell
-- Annotate expressions with their destination buffers
data Dest = Dest { buffer :: BufferId, offset :: Int, size :: Int }

-- Track slice relationships
data SliceMap = SliceMap 
  { argSlices :: Map ArgId Dest
  , retSlices :: Map RetId Dest
  , forwarding :: Map ArgId RetId  -- which arg slices map to which return slices
  }

-- Propagate destinations through the call graph
propagateDests :: CallGraph -> SliceMap -> SliceMap
```

### Papers/Resources:

1. **"Destination-Passing Style for Efficient Memory Management"** - describes DPS in detail
2. **"Region-Based Memory Management"** - Tofte & Talpin
3. **"Linear Types Can Change the World!"** - Wadler (linear types prevent aliasing)
4. **"Stream Fusion"** - Coutts, Leshchinskiy, Stewart (fusion techniques)

### Practical Approach:

For your compiler, I'd suggest:

1. Build a **slice dependency graph** during semantic analysis
2. Use **dataflow analysis** to track which slices flow where
3. Implement **destination propagation** as a compiler pass
4. Use **alias analysis** to prove when forwarding is safe
5. Apply **copy elimination** based on the forwarding map

The combination of these techniques will let you eliminate unnecessary copies while maintaining correctness.

--------------------------------------------------------------------------------

This is highly implementation-dependent and varies across WebAssembly engines, but here are some rough guidelines:

**General estimate: ~10-50 local get/set pairs** might approach the cost of a single `memory.copy` of equivalent data.

**Why locals are faster:**
- **Locals**: Typically map to CPU registers or a very fast stack frame. Each get/set is usually 1-2 CPU instructions.
- **Memory operations**: Involve:
  - Address calculation
  - Bounds checking
  - Cache misses (if data isn't in L1/L2 cache)
  - Potential alignment penalties
  - Memory barrier overhead in some cases

**Rough breakdown:**
- **1-8 locals**: Individual get/set is almost certainly faster
- **8-32 locals**: Individual get/set is likely still faster or comparable
- **32-64 locals**: Starting to be a gray area, depends on the engine
- **64+ locals**: `memory.copy` might start to win, especially if the memory is already hot in cache

**Important caveats:**
1. **Memory.copy has startup overhead** - There's fixed cost for the bounds checking and setup
2. **Small copies favor locals** - For copying just a few values (< 32 bytes), locals win decisively
3. **Large copies favor memory.copy** - For hundreds of bytes, `memory.copy` uses optimized memcpy routines (SIMD, etc.)
4. **Cache matters** - If memory is cold, locals are much faster

**Practical advice**: For typical use cases (saving/restoring < 20 values), stick with individual local operations. Only consider memory if you're copying 50+ values or have profiling data showing it's a bottleneck.
