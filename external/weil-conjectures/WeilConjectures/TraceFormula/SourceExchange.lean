/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.SourceExchangeClass
public import WeilConjectures.TraceFormula.SourceExchangeKernel

/-!

# Exchange of the trace-class sources

For a proper pushforward diagram `(f, g) : (C, c) ⟶ (D, b)` with `q = f × f`, the kernel class of
the coefficient pushforward `[f, g]_! u` is the transported kernel class of `u`
(`ProEtale.CondensedRing.Correspondence.ProperPushforwardDiagram.kernelClass_pushforward`,
blueprint `theorem-proper-pushforward-lefschetz-verdier--1`). It follows from the class of the
coefficient pushforward (`class_pushforward`, identity (b)) and the compatibility of the kernel
pushforward with the Künneth–Verdier isomorphisms
(`ProEtale.CondensedRing.kernelPushforward_comp_kunnethVerdierMap`, identity (a)).

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

section KernelPushforward

variable {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) [IsProper f.left] (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)

/-- Identity (a) read through the inverses of the Künneth–Verdier isomorphisms. -/
lemma classTransportMap_comp_inv_kunnethVerdierMap :
    classTransportMap ℓ f K ≫
        inv (kunnethVerdierMap ℓ ((boundedConstructibleLowerStar ℓ f).obj K)
          ((boundedConstructibleLowerStar ℓ f).obj K)) =
      (boundedConstructibleLowerStar ℓ (prod.map f f)).map (inv (kunnethVerdierMap ℓ K K)) ≫
        kernelPushforward ℓ f K := by
  rewrite [IsIso.comp_inv_eq, Category.assoc, kernelPushforward_comp_kunnethVerdierMap]
  simp only [← Functor.map_comp_assoc (boundedConstructibleLowerStar ℓ (prod.map f f)),
    IsIso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

end KernelPushforward

variable {ℓ} {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence.ProperPushforwardDiagram

variable {c : Correspondence ℓ K} {Y : Over (Spec (.of k))} [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] (P : c.ProperPushforwardDiagram Y)

/-- **The class of the coefficient pushforward** (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`, identity (b)):
`[δ ∘ Rg_* u ∘ γ] = Φ ∘ Rq_* [u] ∘ Ξ ∘ Rb_! η_g`. -/
theorem class_pushforward :
    P.pushforward.class =
      (boundedConstructibleLowerShriek ℓ P.pushforward.support).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ P.g).unit.app (𝟙_ _) ≫
            (boundedConstructibleLowerStar ℓ P.g).map
              (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ P.g)).inv) ≫
        (lowerStarLowerShriekCompIso ℓ P.g_comp_support).hom.app (𝟙_ _) ≫
        (boundedConstructibleLowerStar ℓ (prod.map P.f P.f)).map c.class ≫
        classTransportMap ℓ P.f K := by
  apply classTest_injective
  conv_rhs => rw [classTest_comp, classTest_comp]
  simp only [classTest_map_comp_classTransportMap]
  simp only [Correspondence.class]
  simp only [classTest_correspondenceClassEquiv_symm,
    lowerShriek_map_comp_comp_eqToHom_comp_counit ℓ P.pushforward.support_fst.symm,
    lowerShriek_map_comp_comp_eqToHom_comp_counit ℓ c.support_fst.symm]
  simp only [pushforwardCoeff, pushforwardCoeffCounit, lowerStarUpperShriekExchange]
  simp only [Adjunction.map_comp_mateEquiv_app_comp_counit
    (boundedConstructibleUpperShriekAdjunction ℓ c.c₁)
    (boundedConstructibleUpperShriekAdjunction ℓ P.b₁)]
  have h := congrArg (· ≫ (boundedConstructibleLowerStar ℓ P.f).map
    ((boundedConstructibleLowerShriek ℓ c.c₁).map c.u ≫
      (boundedConstructibleUpperShriekAdjunction ℓ c.c₁).counit.app K)) P.class_pushforward_core
  simpa only [Functor.map_comp, Category.assoc] using h

/-- **Exchange of the trace-class sources** (blueprint
`theorem-proper-pushforward-lefschetz-verdier--1`): the kernel class of the coefficient pushforward
`[f, g]_! u` is the transported kernel class of `u`,
`[[f, g]_! u]_P = ρ_f ∘ Rq_* [u]_P ∘ Ξ ∘ Rb_! η_g`. -/
theorem kernelClass_pushforward :
    P.pushforward.kernelClass =
      (boundedConstructibleLowerShriek ℓ P.pushforward.support).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ P.g).unit.app (𝟙_ _) ≫
            (boundedConstructibleLowerStar ℓ P.g).map
              (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ P.g)).inv) ≫
        (lowerStarLowerShriekCompIso ℓ P.g_comp_support).hom.app (𝟙_ _) ≫
        (boundedConstructibleLowerStar ℓ (prod.map P.f P.f)).map c.kernelClass ≫
        kernelPushforward ℓ P.f K := by
  have h₁ : P.pushforward.kernelClass = P.pushforward.class ≫
      inv (kunnethVerdierMap ℓ P.coeff P.coeff) := supportedClass_eq_class_comp_inv P.pushforward
  have h₂ : c.kernelClass = c.class ≫ inv (kunnethVerdierMap ℓ K K) :=
    supportedClass_eq_class_comp_inv c
  rewrite [h₁, class_pushforward]
  simp only [Category.assoc, classTransportMap_comp_inv_kunnethVerdierMap]
  refine whisker_eq _ (whisker_eq _ ?_)
  simp only [← Functor.map_comp_assoc (boundedConstructibleLowerStar ℓ (prod.map P.f P.f)), h₂]

end Correspondence.ProperPushforwardDiagram

end AlgebraicGeometry.ProEtale.CondensedRing
