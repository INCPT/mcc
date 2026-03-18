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
