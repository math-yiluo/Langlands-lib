/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityScalarPullback
public import WeilConjectures.TateTwist.UpperStarExtendScalars

/-! # Trivialization after changing the coefficient ring -/

@[expose] public section

universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]
  {X U : Scheme.{u}} (g : U ⟶ X)


/-- Change coefficients after extending an isomorphism of pulled-back modules. -/
noncomputable def purityChangeCoefficientPullbackIso
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (e : ((g)^*[Ab.{u + 1}].mapMod _).obj M ≅
      ((g)^*[Ab.{u + 1}].mapMod _).obj N) :
    (g)^*⟦Λ'⟧.obj ((Mod.extendScalars (coefficientMap a X)).obj M) ≅
      (g)^*⟦Λ'⟧.obj ((Mod.extendScalars (coefficientMap a X)).obj N) :=
  ((CondensedRing.pullIso a g).app M).symm ≪≫
    (Mod.extendScalars (coefficientMap a U)).mapIso
      (purityExtendPullbackIso Λ g M N e) ≪≫
    (CondensedRing.pullIso a g).app N

/-- The unit comparison for extension of coefficients, with its monoidal instance fixed. -/
noncomputable def purityCoefficientUnitIso (X : Scheme.{u}) :
    (Mod.extendScalars (coefficientMap a X)).obj (𝟙_ _) ≅ 𝟙_ _ :=
  letI := Mod.extendScalarsMonoidal (coefficientMap a X)
  (Functor.Monoidal.εIso (Mod.extendScalars (coefficientMap a X))).symm

/-- Extend a pulled-back trivialization to the final coefficient ring before specializing it. -/
noncomputable def purityChangeCoefficientTrivialization
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (e : ((g)^*[Ab.{u + 1}].mapMod _).obj M ≅
      ((g)^*[Ab.{u + 1}].mapMod _).obj (𝟙_ _)) :
    (g)^*⟦Λ'⟧.obj ((Mod.extendScalars (coefficientMap a X)).obj M) ≅
      (g)^*⟦Λ'⟧.obj (𝟙_ _) :=
  purityChangeCoefficientPullbackIso Λ a g M (𝟙_ _) e ≪≫
    (g)^*⟦Λ'⟧.mapIso (purityCoefficientUnitIso Λ a X)

variable [WeaklyEtale g] {K : Type u} [Field K] (f : U ⟶ Spec (.of K)) (l : ℕ) [Fact l.Prime]
  {ζ : ℕ → K} (hζ : ∀ n, IsPrimitiveRoot (ζ n) (l ^ n))
  (hζ' : ∀ n, ζ (n + 1) ^ l = ζ n)

/-- The root trivialization with only rational coefficient modules in its result. -/
noncomputable def purityRationalTateTrivialization :
    (g)^*⟦Profinite.padicAlgClRingObj l⟧.obj (tateTwistOne X l) ≅
      (g)^*⟦Profinite.padicAlgClRingObj l⟧.obj (𝟙_ _) :=
  purityChangeCoefficientTrivialization (Profinite.continuousMapRingObj ℤ_[l])
    (Profinite.padicIntRingObjToPadicAlgCl l) g (tateModule X l)
    (upperStarMapModTateModuleIsoUnit g f l hζ hζ' ≪≫ (g)^*[Ab.{u + 1}].mapModUnitIso)

end AlgebraicGeometry.ProEtale
