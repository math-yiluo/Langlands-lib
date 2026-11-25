/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.GraphPieces

/-!

# The trace formula for Frobenius coefficient morphisms in degree one

Let `Φ : X ⟶ X` be a proper endomorphism of a separated `k`-scheme of finite type. For a bounded
constructible `K` and an arbitrary map `ψ : LΦ^* K ⟶ K`, the *trace formula in degree one*
(`ProEtale.CondensedRing.TraceFormulaHolds`) is the identity
```
tr(RΓ_c(X, ψ) ∘ Φ^♯ | RΓ_c(X, K)) = ∑_{x ∈ X(k), Φ x = x} tr(ψ_x | K_x),
```
the statement `TF(X, K, ψ, 1)` of the proof of blueprint
`theorem-trace-formula-frobenius-correspondence--1`, Step 0. For the model Frobenius `Φ` the trace
formula in degree `m` is the trace formula in degree one for the iterate `Φ_m` with the
coefficient map `ψ_m` (`ProEtale.CondensedRing.TraceFormulaHolds.trace_frobeniusCompactOperator`),
and `Φ_m` is again a model Frobenius, over the extension of degree `m` of the finite field.

This file also proves that the stalk maps of the restriction of `ψ` along a morphism
`j : U ⟶ X` with `Φ_U ≫ j = j ≫ Φ` are the stalk maps of `ψ`
(`ProEtale.CondensedRing.trace_graphStalkMap_upperStar`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The *trace formula in degree one* for the proper endomorphism `Φ` of `X` (blueprint
`theorem-trace-formula-frobenius-correspondence--1`, the statement `TF(X, K, ψ, 1)` of Step 0): for
every bounded constructible `K` and every, not necessarily invertible, map `ψ : LΦ^* K ⟶ K`, the
trace of the operator `RΓ_c(X, ψ) ∘ Φ^♯` on `RΓ_c(X, K)` is the sum over the rational points `x`
fixed by `Φ` of the traces of the stalk maps `ψ_x : K_x ⟶ K_x`. The identity is required for all
choices of duals and of the finiteness of the fixed points. -/
def TraceFormulaHolds (Φ : X ⟶ X) [IsProper Φ.left] : Prop :=
  ∀ (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K)
    [HasRightDual
      ((boundedConstructibleLowerShriek ℓ (toPoint X)).obj K)]
    [∀ x : RationalPoint X,
      HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)]
    [Fintype {x : RationalPoint X // x ≫ Φ = x}],
    trace ((compactPullback ℓ Φ).app K ≫
        (boundedConstructibleLowerShriek ℓ (toPoint X)).map ψ) =
      ∑ x : {x : RationalPoint X // x ≫ Φ = x}, trace (Correspondence.graphStalkMap K Φ ψ x.1 x.2)

variable {ℓ}

/-- The trace formula in degree one for the iterate `Φ_m` gives the trace formula in degree `m`
for `Φ`: `tr(F_{c,m}(ψ) | RΓ_c(X, K)) = ∑_{x ∈ X(k), Φ_m x = x} tr(ψ_{m,x} | K_x)`, since
`F_{c,m}(ψ) = RΓ_c(X, ψ_m) ∘ Φ_m^♯` by definition. -/
theorem TraceFormulaHolds.trace_frobeniusCompactOperator {Φ : X ⟶ X} [IsProper Φ.left] {m : ℕ}
    (h : TraceFormulaHolds ℓ (frobeniusIterate Φ m))
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K)
    [Fintype (FixedPoint Φ m)]
    [HasRightDual
      ((boundedConstructibleLowerShriek ℓ (toPoint X)).obj K)]
    [∀ x : RationalPoint X,
      HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)] :
    trace (frobeniusCompactOperator ℓ ψ m) =
      ∑ x : FixedPoint Φ m, trace (Correspondence.graphStalkMap K (frobeniusIterate Φ m)
        (frobeniusCoefficientIterate ψ m) x.1 x.2) :=
  h K (frobeniusCoefficientIterate ψ m)

/-- Coherence of the stalk maps of a restriction, for abstract families of functors with
composition isomorphisms satisfying the associativity laws: the stalk map at `x` of the
restriction of `ψ` along `j'` is conjugate, by the composition isomorphism
`F(x ≫ j') ≅ F(j') ⋙ F(x)`, to the stalk map of `ψ` at `x ≫ j'`. -/
lemma graphStalkMap_upperStar_aux {𝒞 : Type*} [Category 𝒞] {S' U' X' : 𝒞}
    {DS DU DX : Type*} [Category DS] [Category DU] [Category DX]
    (FsU : (S' ⟶ U') → DU ⥤ DS) (FsX : (S' ⟶ X') → DX ⥤ DS)
    (FUU : (U' ⟶ U') → DU ⥤ DU) (FUX : (U' ⟶ X') → DX ⥤ DU) (FXX : (X' ⟶ X') → DX ⥤ DX)
    (csUU : ∀ (a : S' ⟶ U') (b : U' ⟶ U'), FsU (a ≫ b) ≅ FUU b ⋙ FsU a)
    (csUX : ∀ (a : S' ⟶ U') (b : U' ⟶ X'), FsX (a ≫ b) ≅ FUX b ⋙ FsU a)
    (csXX : ∀ (a : S' ⟶ X') (b : X' ⟶ X'), FsX (a ≫ b) ≅ FXX b ⋙ FsX a)
    (cUUX : ∀ (a : U' ⟶ U') (b : U' ⟶ X'), FUX (a ≫ b) ≅ FUX b ⋙ FUU a)
    (cUXX : ∀ (a : U' ⟶ X') (b : X' ⟶ X'), FUX (a ≫ b) ≅ FXX b ⋙ FUX a)
    (AUUX : ∀ (a : S' ⟶ U') (b : U' ⟶ U') (c : U' ⟶ X') (Y : DX),
      (csUX (a ≫ b) c).hom.app Y ≫ (csUU a b).hom.app ((FUX c).obj Y) =
        eqToHom (congrArg (fun f ↦ (FsX f).obj Y) (Category.assoc a b c)) ≫
          (csUX a (b ≫ c)).hom.app Y ≫ (FsU a).map ((cUUX b c).hom.app Y))
    (AUXX : ∀ (a : S' ⟶ U') (b : U' ⟶ X') (c : X' ⟶ X') (Y : DX),
      (csXX (a ≫ b) c).hom.app Y ≫ (csUX a b).hom.app ((FXX c).obj Y) =
        eqToHom (congrArg (fun f ↦ (FsX f).obj Y) (Category.assoc a b c)) ≫
          (csUX a (b ≫ c)).hom.app Y ≫ (FsU a).map ((cUXX b c).hom.app Y))
    {x : S' ⟶ U'} {j' : U' ⟶ X'} {P : U' ⟶ U'} {T : X' ⟶ X'} (hx : x ≫ P = x)
    (hP : P ≫ j' = j' ≫ T) (K0 : DX) (ψ : (FXX T).obj K0 ⟶ K0)
    (e₁ : (FsU x).obj ((FUX j').obj K0) = (FsU (x ≫ P)).obj ((FUX j').obj K0))
    (e₃ : (FUX (P ≫ j')).obj K0 = (FUX (j' ≫ T)).obj K0)
    (e₅ : (FsX (x ≫ j')).obj K0 = (FsX ((x ≫ j') ≫ T)).obj K0) :
    (eqToHom e₅ ≫ (csXX (x ≫ j') T).hom.app K0 ≫ (FsX (x ≫ j')).map ψ) ≫
        (csUX x j').hom.app K0 =
      (csUX x j').hom.app K0 ≫ (eqToHom e₁ ≫ (csUU x P).hom.app ((FUX j').obj K0) ≫
        (FsU x).map (((cUUX P j').inv.app K0 ≫ eqToHom e₃ ≫ (cUXX j' T).hom.app K0) ≫
          (FUX j').map ψ)) := by
  have nat := (csUX x j').hom.naturality ψ
  rw [Functor.comp_map] at nat
  simp only [Functor.map_comp, Category.assoc]
  rw [nat, reassoc_of% (AUXX x j' T K0)]
  simp only [← Category.assoc]
  congr 2
  have hA : (csUU x P).hom.app ((FUX j').obj K0) ≫ (FsU x).map ((cUUX P j').inv.app K0) =
      (csUX (x ≫ P) j').inv.app K0 ≫
        eqToHom (congrArg (fun f ↦ (FsX f).obj K0) (Category.assoc x P j')) ≫
        (csUX x (P ≫ j')).hom.app K0 := by
    rw [← cancel_epi ((csUX (x ≫ P) j').hom.app K0), Iso.hom_inv_id_app_assoc,
      reassoc_of% (AUUX x P j' K0), ← Functor.map_comp, Iso.hom_inv_id_app,
      CategoryTheory.Functor.map_id, Category.comp_id]
  have hcast : ∀ (y : S' ⟶ U') (e : y = x) (b b' : U' ⟶ X') (e' : b = b')
      (h₁ : (FsU x).obj ((FUX j').obj K0) = (FsU y).obj ((FUX j').obj K0))
      (h₂ : (FsX (y ≫ j')).obj K0 = (FsX (x ≫ b)).obj K0)
      (h₃ : (FUX b).obj K0 = (FUX b').obj K0)
      (h₄ : (FsX (x ≫ j')).obj K0 = (FsX (x ≫ b')).obj K0),
      (csUX x j').hom.app K0 ≫ eqToHom h₁ ≫ (csUX y j').inv.app K0 ≫ eqToHom h₂ ≫
          (csUX x b).hom.app K0 ≫ (FsU x).map (eqToHom h₃) =
        eqToHom h₄ ≫ (csUX x b').hom.app K0 := by
    rintro y rfl b _ rfl h₁ h₂ h₃ h₄
    simp
  simp only [Category.assoc]
  rw [reassoc_of% hA, eqToHom_trans_assoc]
  exact (hcast _ hx _ _ hP _ _ _ _).symm

/-- **The stalk maps of a restriction** (blueprint `lemma-additivity-open-subscheme-complement`, the
stalk side, and `lemma-comparison-via-relative-frobenius--4` (3)): for a morphism `j : U ⟶ X` with
`P ≫ j = j ≫ T`, a map `ψ : LT^* K ⟶ K` and a rational point `x` of `U` fixed by `P`, the
stalk map at `x` of the restriction `Lj^* ψ` (composed with the comparison
`LP^* Lj^* K ≅ Lj^* LT^* K`) has the trace of the stalk map of `ψ` at `x ≫ j`. -/
theorem trace_graphStalkMap_upperStar {U : Over (Spec (.of k))} [LocallyOfFiniteType U.hom]
    [QuasiCompact U.hom] [IsSeparated U.hom] {P : U ⟶ U} {T : X ⟶ X} {j : U ⟶ X}
    (hP : P ≫ j = j ≫ T) (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ T).obj K ⟶ K)
    (x : RationalPoint U) (hx : x ≫ P = x)
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K))]
    [HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ
      (x ≫ j)).obj K)] :
    trace (Correspondence.graphStalkMap
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K) P
        ((weilUpperStarComparison ℓ P T j hP).hom.app K ≫
          (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).map ψ) x hx) =
      trace (Correspondence.graphStalkMap K T ψ (x ≫ j)
        (by rw [Category.assoc, ← hP, ← Category.assoc, hx])) := by
  refine (trace_eq_of_iso
    (X := (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ (x ≫ j)).obj K)
    (X' := (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ j).obj K))
    ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ x j).app K) _ _
    ?_).symm
  rw [Correspondence.graphStalkMap, Correspondence.graphStalkMap, weilUpperStarComparison_hom_app]
  exact graphStalkMap_upperStar_aux
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a ↦ boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ a)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b ↦ boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ a b)
    (fun a b c K ↦ boundedConstructibleUpperStarComp_assoc_app _ ℓ a b c K)
    (fun a b c K ↦ boundedConstructibleUpperStarComp_assoc_app _ ℓ a b c K)
    hx hP K ψ _ _ _

end AlgebraicGeometry.ProEtale.CondensedRing
