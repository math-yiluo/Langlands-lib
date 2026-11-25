/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.SmoothProjection

/-!
# The exceptional base change map at the unit for a proper morphism (A1', the proper piece)

For a proper `f : Z ⟶ P` over `k₁` and a cartesian square `πZ ≫ f = f' ≫ πP` over `k₂`, the
compact-support base change isomorphism `Rf_! ⋙ πP^* ≅ πZ^* ⋙ Rf'_!` is proper base change
read through `Rf_! ≅ Rf_*` (`properLowerShriekBaseChangeOfMap`), and the exceptional base change
map at the unit `ProEtale.CondensedRing.smoothUnitBaseChange` attached to it is the library's
`ProEtale.CondensedRing.upperShriekBaseChangeOfMap` at the unit followed by `Rf'^!(e)`
(`smoothUnitBaseChange_proper_eq`). Hence it is invertible for `f` smooth proper along a weakly
étale base change (`isIso_smoothUnitBaseChange_of_smooth_of_weaklyEtale`), in particular for the
projection of a projective space (`isIso_smoothUnitBaseChange_of_projectiveSpace_of_weaklyEtale`),
and for a smooth proper scheme over a point along any change of the base field
(`isIso_smoothUnitBaseChange_of_smooth_point`).

The generic statement is `CategoryTheory.Adjunction.unitBaseChange_ofNatIsoLeft`: `unitBaseChange`
is compatible with the transport of the adjunctions along isomorphisms of the left adjoints.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace CategoryTheory.Adjunction

section OfNatIsoLeft

variable {C C' D D' : Type*} [Category* C] [Category* C'] [Category* D] [Category* D']
  {a : C ⥤ D} {a' : D ⥤ C} (adj : a ⊣ a') {b : C' ⥤ D'} {b' : D' ⥤ C'} (adj' : b ⊣ b')
  {G : C ⥤ C'} {H : D ⥤ D'} {s : C ⥤ D} {s' : C' ⥤ D'} (ι : a ≅ s) (ι' : b ≅ s')
  (bcs : s ⋙ H ⟶ G ⋙ s') [IsIso bcs] {U : D} {U' : D'} (e : H.obj U ⟶ U')

/-- A base change morphism `s H ⟶ s' G` transported along `ι : a ≅ s` and `ι' : b ≅ s'`. -/
abbrev ofNatIsoBaseChange : a ⋙ H ⟶ G ⋙ b :=
  Functor.whiskerRight ι.hom H ≫ bcs ≫ Functor.whiskerLeft G ι'.inv

instance isIso_ofNatIsoBaseChange : IsIso (ofNatIsoBaseChange ι ι' bcs) := by
  unfold ofNatIsoBaseChange
  infer_instance

/-- `CategoryTheory.Adjunction.unitBaseChange` is compatible with the transport of the adjunctions
along isomorphisms of the left adjoints (`CategoryTheory.Adjunction.ofNatIsoLeft`). -/
theorem unitBaseChange_ofNatIsoLeft :
    unitBaseChange adj adj' (ofNatIsoBaseChange ι ι' bcs) e =
      unitBaseChange (adj.ofNatIsoLeft ι) (adj'.ofNatIsoLeft ι') bcs e := by
  symm
  apply eq_unitBaseChange_of_comp_counit
  have h := app_comp_map_unitBaseChange_comp_counit (adj.ofNatIsoLeft ι) (adj'.ofNatIsoLeft ι')
    bcs e
  simp only [ofNatIsoLeft_counit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.comp_obj] at h
  simp only [ofNatIsoBaseChange, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.comp_obj, Category.assoc]
  rw [← ι'.inv.naturality_assoc, h, ← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc]

end OfNatIsoLeft

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section Proper

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {Z P : Over (Spec (.of k₁))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  {Z' P' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom] [IsSeparated Z'.hom]
  [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  (f : Z ⟶ P) (f' : Z' ⟶ P') [IsProper f.left] [IsProper f'.left]
  {πP : P'.left ⟶ P.left} {πZ : Z'.left ⟶ Z.left} (sqf : IsPullback πZ f'.left f.left πP)
  (e : (boundedConstructibleUpperStarOfMap l πP).obj (𝟙_ _) ⟶ 𝟙_ _)

/-- **The compact-support base change isomorphism of a proper morphism across fields**:
proper base change `Rf_* ⋙ πP^* ≅ πZ^* ⋙ Rf'_*`
(`ProEtale.CondensedRing.boundedConstructibleBaseChangeOfMap`) read through `Rf_! ≅ Rf_*`. -/
def properLowerShriekBaseChangeOfMap :
    boundedConstructibleLowerShriek l f ⋙ boundedConstructibleUpperStarOfMap l πP ≅
      boundedConstructibleUpperStarOfMap l πZ ⋙ boundedConstructibleLowerShriek l f' :=
  have := isIso_boundedConstructibleBaseChangeOfMap l sqf
  asIso (Adjunction.ofNatIsoBaseChange (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl l f)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl l f')
    (boundedConstructibleBaseChangeOfMap l sqf.toCommSq))

lemma properLowerShriekBaseChangeOfMap_hom :
    (properLowerShriekBaseChangeOfMap l f f' sqf).hom =
      Adjunction.ofNatIsoBaseChange (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl l f)
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl l f')
        (boundedConstructibleBaseChangeOfMap l sqf.toCommSq) :=
  rfl

/-- **The exceptional base change map at the unit of a proper morphism** is the base change map
of the exceptional inverse image `ProEtale.CondensedRing.upperShriekBaseChangeOfMap` at the unit,
followed by `Rf'^!(e)`. -/
theorem smoothUnitBaseChange_proper_eq :
    smoothUnitBaseChange l f f' (properLowerShriekBaseChangeOfMap l f f' sqf) e =
      (upperShriekBaseChangeOfMap l sqf).app (𝟙_ _) ≫
        (boundedConstructibleUpperShriek l f').map e := by
  have := isIso_boundedConstructibleBaseChangeOfMap l sqf
  change Adjunction.unitBaseChange (boundedConstructibleUpperShriekAdjunction l f)
    (boundedConstructibleUpperShriekAdjunction l f')
    (Adjunction.ofNatIsoBaseChange (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl l f)
      (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl l f')
      (boundedConstructibleBaseChangeOfMap l sqf.toCommSq)) e = _
  rw [Adjunction.unitBaseChange_ofNatIsoLeft]
  rfl

/-- The exceptional base change map at the unit of a proper morphism is invertible as soon as
the base change map of `Rf^!` is invertible at the unit and `e` is invertible. -/
theorem isIso_smoothUnitBaseChange_of_isIso_upperShriekBaseChangeOfMap
    [IsIso ((upperShriekBaseChangeOfMap l sqf).app (𝟙_ _))] [IsIso e] :
    IsIso (smoothUnitBaseChange l f f' (properLowerShriekBaseChangeOfMap l f f' sqf) e) := by
  rw [smoothUnitBaseChange_proper_eq]
  infer_instance

/-- **The proper smooth piece along a weakly étale base change**: for `f` smooth proper of pure
relative dimension `d` and `πP` weakly étale, the exceptional base change map at the unit is
invertible
(`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_smooth_of_weaklyEtale`). -/
theorem isIso_smoothUnitBaseChange_of_smooth_of_weaklyEtale (d : ℕ)
    [SmoothOfRelativeDimension d f.left] [WeaklyEtale πP] [IsIso e] :
    IsIso (smoothUnitBaseChange l f f' (properLowerShriekBaseChangeOfMap l f f' sqf) e) :=
  have := isIso_upperShriekBaseChangeOfMap_app_of_smooth_of_weaklyEtale l d sqf (𝟙_ _)
  isIso_smoothUnitBaseChange_of_isIso_upperShriekBaseChangeOfMap l f f' sqf e

/-- **The projective space piece**: for `f` isomorphic over `P` to the projection
`ℙⁿ_P ⟶ P` and `πP` weakly étale, the exceptional base change map at the unit is invertible. -/
theorem isIso_smoothUnitBaseChange_of_projectiveSpace_of_weaklyEtale (n : ℕ)
    (eP : Z.left ≅ ℙ(ULift.{u} (Fin (n + 1)); P.left))
    (he : eP.hom ≫ ℙ(ULift.{u} (Fin (n + 1)); P.left) ↘ P.left = f.left) [WeaklyEtale πP]
    [IsIso e] :
    IsIso (smoothUnitBaseChange l f f' (properLowerShriekBaseChangeOfMap l f f' sqf) e) :=
  have := isIso_upperShriekBaseChangeOfMap_of_projectiveSpace_of_weaklyEtale l n eP he sqf
  isIso_smoothUnitBaseChange_of_isIso_upperShriekBaseChangeOfMap l f f' sqf e

end Proper

section Point

variable (l : ℕ) [Fact l.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ l)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ l)]
  {Z : Over (Spec (.of k₁))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  {Z' : Over (Spec (.of k₂))} [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom]
  [IsSeparated Z'.hom] (f : Z ⟶ point k₁) (f' : Z' ⟶ point k₂) [IsProper f.left]
  [IsProper f'.left] {πₛ : Spec (.of k₂) ⟶ Spec (.of k₁)} {πZ : Z'.left ⟶ Z.left}
  (sqf : IsPullback πZ f'.left f.left πₛ)
  (e : (boundedConstructibleUpperStarOfMap l (X := point k₁) (Y := point k₂) πₛ).obj (𝟙_ _) ⟶
    𝟙_ _)

/-- **The absolute proper smooth piece across fields**: for a smooth proper `k₁`-scheme of pure
dimension `d` and any `πₛ : Spec k₂ ⟶ Spec k₁`, the exceptional base change map at the unit is
invertible (`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_smooth_point`). -/
theorem isIso_smoothUnitBaseChange_of_smooth_point (d : ℕ) [SmoothOfRelativeDimension d f.left]
    [IsIso e] :
    IsIso (smoothUnitBaseChange l f f' (properLowerShriekBaseChangeOfMap l f f' sqf) e) :=
  have := isIso_upperShriekBaseChangeOfMap_app_of_smooth_point l d sqf (𝟙_ _)
  isIso_smoothUnitBaseChange_of_isIso_upperShriekBaseChangeOfMap l f f' sqf e

end Point

end AlgebraicGeometry.ProEtale.CondensedRing
