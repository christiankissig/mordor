# Symbolic MRD Unit Tests

Comprehensive unit tests for the Symbolic MRD implementation, based on the paper:
**"Symbolic MRD: Dynamic Memory, Undefined Behaviour, and Extrinsic Choice"**

## Overview

These tests validate the core functionality of the Symbolic MRD memory model implementation,
covering all major concepts from the paper including:

- Undefined behavior and compiler optimizations
- Extrinsic choices (alignment, value ranges)
- Dynamic memory allocation and aliasing
- Semantic dependencies (control and data)
- Elaboration operations (value assignment, strengthening, weakening, lifting, forwarding)
- Justifications and execution generation

## Test Organization

### 1. Basic Infrastructure Tests

#### `TestEvents`
Tests basic event creation for all event types:
- Read events (`R`)
- Write events (`W`)
- Branch events (control flow)
- Allocation events (`Alloc`)
- Free events

#### `TestUset` 
Tests the unordered set (uset) implementation:
- Set creation, membership, addition, removal
- Set operations: union, intersection, difference
- Relational operations: cross product, transitive closure
- Acyclicity checking

#### `TestExpressions`
Tests symbolic value and expression representation:
- Value types (numbers, symbols, variables)
- Binary and unary operators
- Disjunctive normal form expressions

#### `TestSolver`
Tests Z3-based constraint solving:
- Satisfiability checking
- Semantic equality
- Implication checking
- Model extraction

### 2. Paper Example Tests

#### `TestExample1_1`: LB+UB+data (§1, §2)
**Paper Section**: Example 1.1, 1.2, 2.1

Tests undefined behavior optimization:
```c
int r1 = x;           |  int r2 = y;
y = 1 / !r1;          |  x = r2;
```

The division `1/!r1` is only defined when `!r1 ≠ 0` (i.e., `r1 = 0`).
The compiler can:
1. **Strengthen**: Add predicate `!r1 ≠ 0`
2. **Value assign**: Substitute `r1 = 0`, transforming `1/!r1` to `1`
3. **Weaken**: Remove the predicate using the UB guarantee

**Tests**:
- Initial justification with data dependency on α
- Optimized justification as independent write

#### `TestExample3_1`: Alignment (§1)
**Paper Section**: Example 3.1, 3.2, 3.3, 3.4

Tests extrinsic choice optimization based on over-alignment:
```c
int* r1 = p;
if (r1 % 16 == 0)
    y = 1;
```

If the compiler chooses to over-align `p` to 16 bytes, the condition
becomes a tautology, allowing the write to be hoisted.

**Tests**:
- Initial justification with control dependency
- Weakened justification using extrinsic guarantee Ω

#### `TestExample4_1`: LB+alias+data (§1)
**Paper Section**: Example 4.1, 4.2

Tests dynamic memory and aliasing:
```c
atomic int x = 0;              |  int r2 = x;
atomic int* p = malloc(...);   |  *p = r2;
int r1 = *p;                   |
x = 1;                         |
```

Allocation guarantees disjointness: `*p` and `x` cannot alias,
enabling reordering despite apparent same-location accesses.

**Tests**:
- Disjointness predicate creation
- Aliasing analysis with malloc

#### `TestExample5_1`: LB+vafalsedep (§1, §2)
**Paper Section**: Example 5.1

Tests control dependency removal through value assignment and lifting:
```c
int r1 = x;              |  int ry = y;
if (r1 == 1)             |  x = ry;
    y = r1;              |
else                     |
    y = 1;               |
```

Both branches write the same value (1) to y, so there's no real
dependency on r1.

**Tests**:
- Initial justifications with control and data dependencies
- Value assignment removing data dependency
- Lifting removing control dependency

#### `TestExample6_1`: FWD (§1, §2)
**Paper Section**: Example 6.1

Tests load forwarding optimization:
```c
int r1 = x;
int r2 = x;
y = r2;
```

The two successive loads can be fused, forwarding r1 to replace r2.

**Tests**:
- Initial justification depending on r2
- Forwarded justification depending on r1 with forwarding edge (1,2)

### 3. Core Mechanism Tests

#### `TestJustifications`
Tests justification structure and semantics:
- Independent writes: `(⊤, ∅) ⊢ w`
- Dependent writes with predicates and dependencies
- Forwarding context: `(P, D) ⊢δ w`
- Write elision context

#### `TestSymbolicEventStructure`
Tests symbolic event structure representation:
- Event set E
- Program order ⊑
- RMW pairs ⊑^rmw
- Program-wide guarantees Ω

#### `TestCoherence`
Tests coherence checking mechanisms:
- RC11 and IMM model support
- Happens-before relation construction
- Sequential consistency checks
- Event identity relations

#### `TestOrigin`
Tests the origin function O(α):
- Finding read events that introduce symbols
- Finding allocation events that introduce pointers
- Handling missing symbols

## Key Concepts from the Paper

### Justifications (§1.2, §4.3)
A justification `(P, D) ⊢δ w` consists of:
- **P**: Control dependency (predicate)
- **D**: Data dependency (set of symbols)
- **δ**: Forwarding context `(f, we)`
- **w**: The write event being justified

### Elaboration Operations (§2, §4.7)

1. **Value Assignment** (va): When `P ⟹ (α = v)`, substitute `v` for `α`
2. **Strengthening** (str): Add arbitrary predicates to P
3. **Weakening** (weak): Remove predicates implied by Ω
4. **Lifting** (lift): Merge equivalent writes from different branches
5. **Forwarding** (fwd): Fuse successive memory accesses

### Semantic Dependencies (§1, §4.5)
The dependency relation `dp` is derived from justifications:
```
dp = ⋃_{j∈J} (O(j_P) ∪ O(j_D)) × {w}
```

### Thin-Air Freedom (§1, §4.6)
Executions must satisfy:
```
acyclic(dp ∪ ≤ ∪ rf)
```
where:
- `dp`: Semantic dependencies
- `≤`: Preserved program order
- `rf`: Reads-from relation

## References

1. **Paper**: "Symbolic MRD: Dynamic Memory, Undefined Behaviour, and Extrinsic Choice"
2. **RC11**: Lahav et al., "Repairing Sequential Consistency in C/C++11", PLDI 2017
3. **MRD**: Paviotti et al., "Modular Relaxed Dependencies in Weak Memory Concurrency", ESOP 2020
