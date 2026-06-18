# Sabok S-prime Obstructions in Lean

A work-in-progress Lean 4 formalization of the algebraic and metric core of the draft:

> *Finite and Urysohn obstructions to Sabok's S-prime simplex questions*

## Status

The current source file has been checked successfully by the real Lean checker.

- Lean: `v4.30.0`
- Mathlib: `v4.30.0`
- No `sorry`
- No `admit`
- No project-defined axioms

This repository currently formalizes the verified core obstruction arguments. It is **not yet a complete machine-checked formalization of the paper’s final statements about \(S'(X)\), Choquet simplices, or the Poulsen simplex**.

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

The main verified endpoint is:

```lean
theorem rational_urysohn_core_obstruction
```

## Not yet completed

The following parts are planned but are not currently claimed as verified:

- the general finite distance-row model;
- the affine-independence and affine-kernel criterion;
- the proof that distance rows are vertices of the finite row polytope;
- the sharp finite threshold:
  - all spaces with at most three points give simplices;
  - counterexamples exist in every finite cardinality at least four;
- convexity, closedness, compactness, and metrizability of the Katětov compactum;
- finite rational Katětov approximation and density of distance profiles;
- the identification
  \[
  S'_D(\mathbb U_1)=K(D);
  \]
- instantiation with the rational Urysohn sphere and its completion;
- the bridge from midpoint extremality to the standard extreme-point definition;
- probability measures and barycentric representations;
- the final conclusions that \(S'(\mathbb U_1)\) is not a Choquet simplex and is not the Poulsen simplex.

These parts are **coming soon**.

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