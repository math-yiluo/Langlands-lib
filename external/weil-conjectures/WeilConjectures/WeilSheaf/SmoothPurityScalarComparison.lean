/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityRationalTrivialization
public import WeilConjectures.WeilSheaf.SmoothPurityPullbackForgetFactor
import WeilConjectures.Tactic.ExactModProofs

/-! # Component comparisons used in scalar Frobenius transport -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {X U : Scheme.{u}} (p : U ⟶ X) (s : U ⟶ U) (hs : s ≫ p = p)

/-- The underlying abelian-sheaf factorization of the geometric Frobenius pullback. -/
noncomputable def purityAbelianFactorIso :
    (p)^*[Ab.{u + 1}] ⋙
        (s)^*[Ab.{u + 1}] ≅
      (p)^*[Ab.{u + 1}] :=
  (ProEtale.upperStarComp' Ab.{u + 1} s
    p p
    hs.symm).symm

/-- The module pullback factorization attached to s ≫ p = p. -/
noncomputable def purityModuleFactorIso :
    (p)^*⟦Λ⟧ ⋙ (s)^*⟦Λ⟧ ≅ (p)^*⟦Λ⟧ :=
  (CondensedRing.upperStarComp Λ s p).symm ≪≫ CondensedRing.upperStarCongr Λ hs

/-- The factor square in the component spelling used by faithful transport. -/
lemma purity_upperStarForgetIso_factor_normalized
    (M : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    (s)^*[Ab.{u + 1}].map ((CondensedRing.upperStarForgetIso Λ p).hom.app M) ≫
        (CondensedRing.upperStarForgetIso Λ s).hom.app ((p)^*⟦Λ⟧.obj M) ≫
        (Mod.forget (condensedRingObj Λ U)).map ((purityModuleFactorIso Λ p s hs).hom.app M) =
      (purityAbelianFactorIso p s hs).hom.app M.X ≫
        (CondensedRing.upperStarForgetIso Λ p).hom.app M := by
  have h := CondensedRing.purity_upperStarForgetIso_factor_hom Λ p s hs M
  simp only [Category.assoc, purityModuleFactorIso, purityAbelianFactorIso] at h ⊢
  dsimp only [Functor.comp_obj, Functor.comp_map, Mod.forget] at h ⊢
  cast_proofs h

/-- The extension-unit square in the component spelling used by faithful transport. -/
lemma purityExtendPullbackIso_forget
    (M N : Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (e : ((p)^*[Ab.{u + 1}].mapMod _).obj M ≅
      ((p)^*[Ab.{u + 1}].mapMod _).obj N) :
    (CondensedRing.upperStarForgetIso Λ p).hom.app M ≫
        (Mod.forget (condensedRingObj Λ U)).map (purityExtendPullbackIso Λ p M N e).hom =
      e.hom.hom ≫ (CondensedRing.upperStarForgetIso Λ p).hom.app N := by
  have h := purityExtendPullbackIso_unit Λ p M N e
  simp only [CondensedRing.upperStarForgetIso_hom_app,
    Mod.forget, purityPullbackUnit] at h ⊢
  dsimp only [Functor.comp_obj, Functor.comp_map, Mod.forget] at h ⊢
  cast_proofs h

end AlgebraicGeometry.ProEtale
