# Sabok S-prime Obstructions in Lean

A work-in-progress Lean 4 formalization of the algebraic and metric core of the draft:

> *Finite and Urysohn obstructions to Sabok's S-prime simplex questions*

## Verified baseline

The progress reported here is based only on:

```text
LeanWorkspace/SabokSPrime.lean
```

This file was checked successfully by the real Lean checker on 2026-06-19.

- Lean: `v4.30.0`
- Mathlib: `v4.30.0`
- Checker result: 0 errors, 2 non-blocking linter warnings
- No `sorry`
- No `admit`
- No project-defined axioms

The current development formalizes the verified core obstruction arguments. It
is **not yet a complete machine-checked formalization of the paper’s final
statements about \(S'(X)\), Choquet simplices, or the Poulsen simplex**.

## What is verified

### The finite \(C_4\) obstruction

The formalization includes:

- the diameter-one four-cycle distance matrix;
- the affine row relation
  \[
  r_0+r_2=r_1+r_3;
  \]
- two distinct probability vectors supported on opposite pairs;
- a proof that both vectors have the same distance-row barycenter;
- an explicit witness to failure of unique barycentric coordinates.

### The Katětov obstruction core

For a pseudometric space satisfying a diameter-one bound and an exact rational finite one-point extension property, the formalization includes:

- bounded Katětov functions;
- tight-inequality lemmas used in extremality arguments;
- construction of side-one equilateral triangles;
- midpoint extremality of the constant functions \(1\) and \(1/2\);
- the half-radius functions
  \[
  f_A(x)=\min\{1,\tfrac12+d(x,A)\},
  \qquad
  g_A(x)=\max\{\tfrac12,1-d(x,A)\};
  \]
- proofs that \(f_A\) and \(g_A\) are bounded Katětov functions;
- the identity
  \[
  f_A+g_A=1+\tfrac12;
  \]
- extremality of \(f_A\) and \(g_A\);
- the plateau-triangle construction required for the extremality of \(g_A\);
- two genuinely different extreme midpoint representations;
- an abstract Urysohn-style core obstruction derived from the extension property.

### The convex extreme-point bridge

The bounded Katětov functions are now available as a named set, and the custom
`MidpointExtreme` predicate is bridged to Mathlib's standard notion:

- the concrete convex set
  \[
  \mathrm{katetovSet}(D)=\{f:\ D\to\mathbb R\mid f\text{ is a bounded Katětov function}\};
  \]
- a proof that `katetovSet` is convex;
- the equivalence
  \[
  \mathrm{MidpointExtreme}(e)\ \Longleftrightarrow\ e\in\mathrm{extremePoints}(\mathrm{katetovSet}(D)),
  \]
  i.e. the midpoint characterization agrees with Mathlib's
  `Set.extremePoints` because the set is convex.

### Two-point non-uniqueness on the standard extreme boundary

The non-uniqueness obstruction is reformulated entirely with standard extreme
points and packaged as a refutation of equal-weight two-point uniqueness:

- two genuinely different unordered pairs of standard extreme points sharing the
  same equal-weight barycenter;
- an equivalence between the internal midpoint obstruction and the
  standard-extreme-point formulation;
- the Urysohn construction gives two distinct equal-weight two-point
  representations on the standard extreme boundary;
- a formal conclusion that equal-weight two-point uniqueness fails.

This is the finite-support precursor to the paper's measure-theoretic statement;
probability measures and their barycenters are not yet represented with
Mathlib's measure API.

The main verified endpoints are:

```lean
theorem rational_urysohn_core_obstruction
theorem rational_urysohn_not_uniqueExtremeMidpointRepresentation
```

## Not yet completed

The following parts are planned but are not currently claimed as verified:

- the general finite distance-row model;
- the affine-independence and affine-kernel criterion;
- the proof that distance rows are vertices of the finite row polytope;
- the sharp finite threshold:
  - all spaces with at most three points give simplices;
  - counterexamples exist in every finite cardinality at least four;
- closedness, compactness, and metrizability of the Katětov compactum;
- finite rational Katětov approximation and density of distance profiles;
- the identification
  \[
  S'_D(\mathbb U_1)=K(D);
  \]
- instantiation with the rational Urysohn sphere and its completion;
- probability measures and barycentric representations;
- the final conclusions that \(S'(\mathbb U_1)\) is not a Choquet simplex and is not the Poulsen simplex.

These items are remaining work and are not part of the verified baseline.

## Verification

From the Lake project directory:

```text
lake env lean LeanWorkspace/SabokSPrime.lean
```

The file can also be included in the library build through:

```text
lake build
```

## Scope

The current development should be viewed as a verified library of the novel finite and Katětov obstruction mechanisms. The topological and Choquet-theoretic bridge to the full statement about Sabok’s \(S'\) remains future work.
