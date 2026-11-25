/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.BorelMoore
public import WeilConjectures.TraceFormula.ProperKunneth
public import WeilConjectures.TraceFormula.ProperPushforward
public import WeilConjectures.TraceFormula.TraceClass

/-!

# Kernel maps of a proper pushforward diagram

Let `(f, g) : (C, c) ⟶ (D, b)` be a proper pushforward diagram of an endocorrespondence `c` of
`(X, K)`, with `K' = Rf_* K`, the induced proper map of fixed loci `h : Fix(c) ⟶ Fix(b)` and
`q = f × f : X ⨯ X ⟶ Y ⨯ Y`. This file defines the remaining maps of blueprint
`theorem-proper-pushforward-lefschetz-verdier--1` (the trace `τ_f`, the multiplication `μ_f`, the
composition isomorphism `Ξ` and the exchange `E` are in
`WeilConjectures.TraceFormula.ProperPushforward`):

* the *dual pushforward* `χ_f : Rf_* D_X K ⟶ D_Y K'` (`lowerStarVerdierDualMap`);
* the *kernel pushforward* `ρ_f = (1 ⊠ χ_f) ∘ Π_f⁻¹ : Rq_* P_X ⟶ P_Y` (`kernelPushforward`), where
  `Π_f : K' ⊠ Rf_* D_X K ⟶ Rq_* (K ⊠ D_X K)` is the Künneth map, an isomorphism by the relative
  product theorem (`prodLowerStarExternalProduct`, `isIso_prodLowerStarExternalProduct`,
  blueprint `lemma-kunneth-formula-compact-supports--1`, in
  `WeilConjectures.TraceFormula.ProperKunneth`);
* the *kernel class* `[u]_P : Rc_! ℚ̄_ℓ,C ⟶ P_X` (`Correspondence.kernelClass`), the exceptional
  adjoint of the mate of `u` followed by the external duality isomorphism;
* the *support isomorphism* `ζ_c : Rι_* ω_Fix(c) ≅ Rc^! RΔ_* ω_X`
  (`Correspondence.FixedLocus.supportIso`);

and the *proper pushforward of the trace class* `h_* Tr_c(u)`
(`Correspondence.ProperPushforwardDiagram.traceClassPushforward`, blueprint
`definition-pushforward-correspondence`, `definition-pushforward-correspondence--2`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-! ### Maps along proper morphisms -/

section ProperMaps

variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]

/-- The *dual pushforward* `χ_f : Rf_* D_X K ⟶ D_Y (Rf_* K)` along a proper morphism (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, item 4): the tensor–hom transpose of
```
Rf_* K ⊗ Rf_* D_X K --μ_f--> Rf_* (K ⊗ D_X K) --Rf_* ev--> Rf_* ω_X --τ_f--> ω_Y.
```
-/
noncomputable def lowerStarVerdierDualMap (f : X ⟶ Y) [IsProper f.left]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerStar ℓ f).obj (verdierDual ℓ K) ⟶
      verdierDual ℓ ((boundedConstructibleLowerStar ℓ f).obj K) :=
  curry (lowerStarTensorMap ℓ f K _ ≫
    (boundedConstructibleLowerStar ℓ f).map ((ihom.ev K).app (dualizingComplex' ℓ X)) ≫
    lowerStarDualizingComplexTrace ℓ f)

/-- The *kernel pushforward* `ρ_f = (1 ⊠ χ_f) ∘ Π_f⁻¹ : Rq_* (K ⊠ D_X K) ⟶ K' ⊠ D_Y K'` along a
proper morphism `f`, `q = f × f`, `K' = Rf_* K` (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, item 5). -/
noncomputable def kernelPushforward (f : X ⟶ Y) [IsProper f.left]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerStar ℓ (prod.map f f)).obj
        (externalProduct ℓ K (verdierDual ℓ K)) ⟶
      externalProduct ℓ ((boundedConstructibleLowerStar ℓ f).obj K)
        (verdierDual ℓ ((boundedConstructibleLowerStar ℓ f).obj K)) :=
  inv (prodLowerStarExternalProduct ℓ f f K (verdierDual ℓ K)) ≫
    (_ ◁ (boundedConstructibleUpperStar _ ℓ (prod.snd : Y ⨯ Y ⟶ Y)).map
      (lowerStarVerdierDualMap ℓ f K))

end ProperMaps

/-! ### Kernel classes and support isomorphisms -/

variable {ℓ} {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence

variable (c : Correspondence ℓ K)

/-- The *kernel class* `[u]_P : Rc_! ℚ̄_ℓ,C ⟶ K ⊠ D_X K` of an endocorrespondence (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, item 7): the exceptional adjoint of
`ℚ̄_ℓ,C --ũ--> 𝓗_c(K) ≅ Rc^! (K ⊠ D_X K)`. -/
noncomputable def kernelClass :
    (boundedConstructibleLowerShriek ℓ c.support).obj (𝟙_ _) ⟶
      externalProduct ℓ K (verdierDual ℓ K) :=
  ((boundedConstructibleUpperShriekAdjunction ℓ c.support).homEquiv _ _).symm
    (c.mate ≫ c.verdierDualityIso.hom)

namespace FixedLocus

variable {c} (F : c.FixedLocus)

/-- The *support isomorphism* `ζ_c : Rι_* ω_Fix(c) ≅ Rc^! RΔ_* ω_X` (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, item 8): the inverse of the right-adjoint form of
base change in the fixed square followed by `Rd^! ω_X ≅ ω_Fix(c)`. -/
noncomputable def supportIso :
    (boundedConstructibleLowerStar ℓ F.ι).obj (dualizingComplex' ℓ F.F) ≅
      (boundedConstructibleUpperShriek ℓ c.support).obj
        ((boundedConstructibleLowerStar ℓ (diag X)).obj (dualizingComplex' ℓ X)) :=
  (F.upperShriekLowerStarIso.app (dualizingComplex' ℓ X) ≪≫
    (boundedConstructibleLowerStar ℓ F.ι).mapIso (dualizingComplexComp ℓ F.d)).symm

end FixedLocus

/-- By construction, the trace morphism is `ζ_c⁻¹ ∘ Rc^! δ_K ∘ ξ` (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, last paragraph). -/
lemma traceMap_eq (F : c.FixedLocus) :
    c.traceMap F = c.verdierDualityIso.hom ≫
      (boundedConstructibleUpperShriek ℓ c.support).map (evaluationKernel ℓ K) ≫
      F.supportIso.inv :=
  rfl

namespace ProperPushforwardDiagram

variable {c} {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] (P : c.ProperPushforwardDiagram Y) (Fc : c.FixedLocus)
  (Fb : P.pushforward.FixedLocus)

/-- The *proper pushforward of the trace class* `h_* Tr_c(u) : ℚ̄_ℓ,Fix(b) ⟶ ω_Fix(b)` along the
induced proper map of fixed loci `h : Fix(c) ⟶ Fix(b)` (blueprint
`definition-pushforward-correspondence`, `definition-pushforward-correspondence--2`): the
Borel–Moore pushforward of the trace class. -/
noncomputable def traceClassPushforward : BorelMooreSection ℓ Fb.F :=
  BorelMooreSection.pushforward (P.fixMap Fc Fb) (c.traceClass Fc)

end ProperPushforwardDiagram

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
