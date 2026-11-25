/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.WeaklyEtale
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionTensorMap

/-!

# Base change of exceptional inverse images and composition

Let `f : Z ⟶ Y` and `g : Y ⟶ P` be proper morphisms of separated schemes of finite type over a
field `k₁`, with base changes `f' : Z' ⟶ Y'` and `g' : Y' ⟶ P'` (over a field `k₂`) in stacked
cartesian squares
```
Z' --πZ--> Z
 |f'       |f
 v         v
Y' --πY--> Y
 |g'       |g
 v         v
P' --πP--> P
```
This file proves that the base change maps of the exceptional inverse image
`β : πZ^* Rf^! ⟶ Rf'^! πP^*` (`ProEtale.CondensedRing.upperShriekBaseChangeOfMap`) are compatible
with composition.

## Main results

- `ProEtale.CondensedRing.upperShriekBaseChangeOfMap_comp_app`: through the composition
  isomorphisms `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!`
  (`ProEtale.CondensedRing.boundedConstructibleUpperShriekComp_padicAlgCl`), `β_{f ≫ g}(M)` is
  `β_f(Rg^! M)` followed by `Rf'^!(β_g(M))`.
- `ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_comp_app_iff`: if `β_f` is invertible
  at `Rg^! M`, then `β_{f ≫ g}(M)` is invertible if and only if `Rf'^!(β_g(M))` is.
- `ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_comp_app`: `β_{f ≫ g}(M)` is invertible
  if `β_f(Rg^! M)` and `β_g(M)` are; in particular, for a closed immersion `f`, if `β_g(M)` is,
  along weakly étale base change
  (`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_comp_app_of_weaklyEtale`) or a field
  extension (`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_comp_app_of_fieldExtension`).

## Proof

The adjunctions `Rf_* ⊣ Rf^!` (`ProEtale.CondensedRing.lowerStarUpperShriekAdjunction`) compose,
and the inverse proper base change isomorphisms paste
(`ProEtale.CondensedRing.boundedConstructibleBaseChangeOfMap_app_comp_lowerStarCompOfEq_inv_app`),
so the mates paste through the isomorphisms of right adjoints induced by `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*`
(`CategoryTheory.Adjunction.mateEquiv_inv_comp_rightAdjointUniq`). These isomorphisms are the
composition isomorphisms of the exceptional inverse image, since `Rf_! ≅ Rf_*` is compatible with
composition (`ProEtale.CondensedRing.boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_comp`);
this is the abstract
`CategoryTheory.Adjunction.rightAdjointUniq_ofNatIsoLeft_comp_eq_conjugateIsoEquiv`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace CategoryTheory.Adjunction

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]

/-- **Conjugate composition isomorphisms and changes of left adjoints.** Let `Li ⊣ Ri`,
`La ⊣ Ra`, `Lb ⊣ Rb` be adjunctions with a composition isomorphism `c : Lb ≅ Li ⋙ La`, and let
`ei : Li ≅ Si`, `ea : La ≅ Sa`, `eb : Lb ≅ Sb` be identifications with functors having a
composition isomorphism `s : Si ⋙ Sa ≅ Sb` compatible with `c`. Then the isomorphism
`Rb ≅ Ra ⋙ Ri` of right adjoints of `Sb ≅ Si ⋙ Sa` is the conjugate of `c`. -/
lemma rightAdjointUniq_ofNatIsoLeft_comp_eq_conjugateIsoEquiv {Li : C ⥤ D} {Ri : D ⥤ C}
    {La : D ⥤ E} {Ra : E ⥤ D} {Lb : C ⥤ E} {Rb : E ⥤ C} (adji : Li ⊣ Ri) (adja : La ⊣ Ra)
    (adjb : Lb ⊣ Rb) (c : Lb ≅ Li ⋙ La) {Si : C ⥤ D} {Sa : D ⥤ E} {Sb : C ⥤ E} (ei : Li ≅ Si)
    (ea : La ≅ Sa) (eb : Lb ≅ Sb) (s : Si ⋙ Sa ≅ Sb)
    (hcomp : ∀ K, c.hom.app K ≫ ea.hom.app (Li.obj K) ≫ Sa.map (ei.hom.app K) =
      eb.hom.app K ≫ s.inv.app K) :
    rightAdjointUniq ((adjb.ofNatIsoLeft eb).ofNatIsoLeft s.symm)
        ((adji.ofNatIsoLeft ei).comp (adja.ofNatIsoLeft ea)) =
      conjugateIsoEquiv adjb (adji.comp adja) c.symm := by
  refine Iso.ext ?_
  rw [← Iso.inv_eq_inv]
  ext N
  apply ext_of_comp_counit (adj := adjb.ofNatIsoLeft eb)
  have h₁ := map_conjugateIsoEquiv_inv_app_comp_inv_app_comp_counit_app adji adja adjb c ei ea
    eb s hcomp N
  have h₂ := rightAdjointUniq_hom_app_counit ((adji.ofNatIsoLeft ei).comp (adja.ofNatIsoLeft ea))
    ((adjb.ofNatIsoLeft eb).ofNatIsoLeft s.symm) N
  have h₃ := s.hom.naturality ((rightAdjointUniq ((adji.ofNatIsoLeft ei).comp
    (adja.ofNatIsoLeft ea)) ((adjb.ofNatIsoLeft eb).ofNatIsoLeft s.symm)).hom.app N)
  simp only [ofNatIsoLeft_counit, NatTrans.comp_app, Functor.whiskerLeft_app, comp_counit_app,
    Iso.symm_inv, Functor.comp_map, Functor.comp_obj] at h₂ h₃ ⊢
  rw [rightAdjointUniq_inv_app, h₁, ← cancel_epi (s.hom.app _), ← reassoc_of% h₃, h₂]
  simp

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

/-! ### Composition isomorphisms of exceptional inverse images -/

section CompIso

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {Z Y P : Over (Spec (.of k))} [LocallyOfFiniteType Z.hom]
  [QuasiCompact Z.hom] [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]

/-- The composition isomorphism `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` for the equality `f ≫ g = f ≫ g` is
`ProEtale.CondensedRing.boundedConstructibleLowerStarComp`. -/
lemma boundedConstructibleLowerStarCompOfEq_rfl (f : Z ⟶ Y) (g : Y ⟶ P) :
    boundedConstructibleLowerStarCompOfEq ℓ f g rfl = boundedConstructibleLowerStarComp ℓ f g := by
  ext
  simp [boundedConstructibleLowerStarCompOfEq]

/-- The composition isomorphism `R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!` is the isomorphism of right adjoints
of `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*`, for the adjunctions `Rf_* ⊣ Rf^!`
(`ProEtale.CondensedRing.lowerStarUpperShriekAdjunction`). -/
lemma rightAdjointUniq_lowerStarUpperShriekAdjunction_comp (f : Z ⟶ Y) (g : Y ⟶ P)
    [IsProper f.left] [IsProper g.left] [IsProper (f ≫ g).left] :
    Adjunction.rightAdjointUniq ((lowerStarUpperShriekAdjunction ℓ (f ≫ g)).ofNatIsoLeft
        (boundedConstructibleLowerStarComp ℓ f g).symm)
      ((lowerStarUpperShriekAdjunction ℓ f).comp (lowerStarUpperShriekAdjunction ℓ g)) =
      boundedConstructibleUpperShriekComp_padicAlgCl ℓ f g :=
  Adjunction.rightAdjointUniq_ofNatIsoLeft_comp_eq_conjugateIsoEquiv _ _ _ _ _ _ _ _
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl_comp ℓ f g)

end CompIso

/-! ### Base change maps and composition -/

section Comp

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)] [Fact (ringChar k₂).Prime]
  [Fact (ringChar k₂ ≠ ℓ)]
  {Z Y P : Over (Spec (.of k₁))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  {Z' Y' P' : Over (Spec (.of k₂))} [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom]
  [IsSeparated Z'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  {f : Z ⟶ Y} {g : Y ⟶ P} {f' : Z' ⟶ Y'} {g' : Y' ⟶ P'} [IsProper f.left] [IsProper g.left]
  [IsProper f'.left] [IsProper g'.left] [IsProper (f ≫ g).left] [IsProper (f' ≫ g').left]
  {πZ : Z'.left ⟶ Z.left} {πY : Y'.left ⟶ Y.left} {πP : P'.left ⟶ P.left}

/-- **Base change maps of exceptional inverse images and composition**: for proper morphisms
`f : Z ⟶ Y`, `g : Y ⟶ P` and their base changes `f'`, `g'` in stacked cartesian squares, the base
change map `β_{f ≫ g}(M) : πZ^* R(f ≫ g)^! M ⟶ R(f' ≫ g')^! πP^* M`
(`ProEtale.CondensedRing.upperShriekBaseChangeOfMap`) is, through the composition isomorphisms
`R(f ≫ g)^! ≅ Rg^! ⋙ Rf^!`, the composite of `β_f(Rg^! M)` and `Rf'^!(β_g(M))`. -/
theorem upperShriekBaseChangeOfMap_comp_app (sqf : IsPullback πZ f'.left f.left πY)
    (sqg : IsPullback πY g'.left g.left πP) (sqfg : IsPullback πZ (f' ≫ g').left (f ≫ g).left πP)
    (M : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarOfMap ℓ πZ).map
        ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ f g).hom.app M) ≫
      (upperShriekBaseChangeOfMap ℓ sqf).app ((boundedConstructibleUpperShriek ℓ g).obj M) ≫
      (boundedConstructibleUpperShriek ℓ f').map ((upperShriekBaseChangeOfMap ℓ sqg).app M) =
    (upperShriekBaseChangeOfMap ℓ sqfg).app M ≫
      (boundedConstructibleUpperShriekComp_padicAlgCl ℓ f' g').hom.app
        ((boundedConstructibleUpperStarOfMap ℓ πP).obj M) := by
  have := isIso_boundedConstructibleBaseChangeOfMap ℓ sqf
  have := isIso_boundedConstructibleBaseChangeOfMap ℓ sqg
  have := isIso_boundedConstructibleBaseChangeOfMap ℓ sqfg
  have hEx : Adjunction.ExchangeCompCompatible
      (boundedConstructibleBaseChangeOfMap ℓ sqf.toCommSq)
      (boundedConstructibleBaseChangeOfMap ℓ sqg.toCommSq)
      (boundedConstructibleBaseChangeOfMap ℓ sqfg.toCommSq)
      (boundedConstructibleLowerStarComp ℓ f g).symm
      (boundedConstructibleLowerStarComp ℓ f' g').symm := ⟨fun N ↦ by
    have h := boundedConstructibleBaseChangeOfMap_app_comp_lowerStarCompOfEq_inv_app ℓ rfl rfl
      sqf.toCommSq sqg.toCommSq sqfg.toCommSq N
    simp only [boundedConstructibleLowerStarCompOfEq_rfl] at h
    exact h.symm⟩
  have key := Adjunction.mateEquiv_inv_comp_rightAdjointUniq
    (lowerStarUpperShriekAdjunction ℓ f) (lowerStarUpperShriekAdjunction ℓ g)
    (lowerStarUpperShriekAdjunction ℓ (f ≫ g)) (lowerStarUpperShriekAdjunction ℓ f')
    (lowerStarUpperShriekAdjunction ℓ g') (lowerStarUpperShriekAdjunction ℓ (f' ≫ g'))
    _ _ _ _ _ hEx M
  rw [rightAdjointUniq_lowerStarUpperShriekAdjunction_comp,
    rightAdjointUniq_lowerStarUpperShriekAdjunction_comp] at key
  exact key

/-- **Invertibility of base change maps of a composite**: if the base change map `β_f` of the
exceptional inverse image is invertible at `Rg^! M`, then `β_{f ≫ g}` is invertible at `M` if and
only if `Rf'^!(β_g(M))` is. -/
theorem isIso_upperShriekBaseChangeOfMap_comp_app_iff (sqf : IsPullback πZ f'.left f.left πY)
    (sqg : IsPullback πY g'.left g.left πP) (sqfg : IsPullback πZ (f' ≫ g').left (f ≫ g).left πP)
    (M : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (hf : IsIso ((upperShriekBaseChangeOfMap ℓ sqf).app
      ((boundedConstructibleUpperShriek ℓ g).obj M))) :
    IsIso ((upperShriekBaseChangeOfMap ℓ sqfg).app M) ↔
      IsIso ((boundedConstructibleUpperShriek ℓ f').map
        ((upperShriekBaseChangeOfMap ℓ sqg).app M)) := by
  rw [← isIso_comp_right_iff _ ((boundedConstructibleUpperShriekComp_padicAlgCl ℓ f' g').hom.app
      ((boundedConstructibleUpperStarOfMap ℓ πP).obj M)),
    ← upperShriekBaseChangeOfMap_comp_app ℓ sqf sqg sqfg M, isIso_comp_left_iff,
    isIso_comp_left_iff]

/-- **Base change maps of a composite**: if the base change maps of the exceptional inverse
images `β_f` and `β_g` are invertible at `Rg^! M` and at `M`, then `β_{f ≫ g}` is invertible at
`M`. -/
theorem isIso_upperShriekBaseChangeOfMap_comp_app (sqf : IsPullback πZ f'.left f.left πY)
    (sqg : IsPullback πY g'.left g.left πP) (sqfg : IsPullback πZ (f' ≫ g').left (f ≫ g).left πP)
    (M : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    [IsIso ((upperShriekBaseChangeOfMap ℓ sqf).app ((boundedConstructibleUpperShriek ℓ g).obj M))]
    [IsIso ((upperShriekBaseChangeOfMap ℓ sqg).app M)] :
    IsIso ((upperShriekBaseChangeOfMap ℓ sqfg).app M) :=
  (isIso_upperShriekBaseChangeOfMap_comp_app_iff ℓ sqf sqg sqfg M inferInstance).2 inferInstance

/-- **Closed immersions followed by maps along weakly étale base change**: for a closed immersion
`i : Z ⟶ Y`, a proper `g : Y ⟶ P` and a weakly étale `πY`, the base change map
`β_{i ≫ g}(M)` is invertible if `β_g(M)` is
(`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_weaklyEtale`). -/
theorem isIso_upperShriekBaseChangeOfMap_comp_app_of_weaklyEtale [IsClosedImmersion f.left]
    [IsClosedImmersion f'.left] [WeaklyEtale πY] (sqf : IsPullback πZ f'.left f.left πY)
    (sqg : IsPullback πY g'.left g.left πP) (sqfg : IsPullback πZ (f' ≫ g').left (f ≫ g).left πP)
    (M : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    [IsIso ((upperShriekBaseChangeOfMap ℓ sqg).app M)] :
    IsIso ((upperShriekBaseChangeOfMap ℓ sqfg).app M) :=
  have := isIso_upperShriekBaseChangeOfMap_app_of_weaklyEtale ℓ sqf
    ((boundedConstructibleUpperShriek ℓ g).obj M)
  isIso_upperShriekBaseChangeOfMap_comp_app ℓ sqf sqg sqfg M

end Comp

/-! ### Field extensions -/

section FieldExtension

variable (ℓ : ℕ) [Fact ℓ.Prime] {F L : Type u} [Field F] [Field L] [Algebra F L]
  [Fact (ringChar F).Prime] [Fact (ringChar F ≠ ℓ)] [Fact (ringChar L).Prime]
  [Fact (ringChar L ≠ ℓ)]
  {Z Y P : Over (Spec (.of F))} [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType P.hom] [QuasiCompact P.hom] [IsSeparated P.hom]
  {Z' Y' P' : Over (Spec (.of L))} [LocallyOfFiniteType Z'.hom] [QuasiCompact Z'.hom]
  [IsSeparated Z'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  [LocallyOfFiniteType P'.hom] [QuasiCompact P'.hom] [IsSeparated P'.hom]
  {i : Z ⟶ Y} {g : Y ⟶ P} {i' : Z' ⟶ Y'} {g' : Y' ⟶ P'} [IsClosedImmersion i.left]
  [IsClosedImmersion i'.left] [IsProper g.left] [IsProper g'.left] [IsProper (i ≫ g).left]
  [IsProper (i' ≫ g').left]
  {πZ : Z'.left ⟶ Z.left} {πY : Y'.left ⟶ Y.left} {πP : P'.left ⟶ P.left}

/-- **Closed immersions followed by maps along a field extension**: for a closed immersion
`i : Z ⟶ Y`, a proper `g : Y ⟶ P` of `F`-schemes and their base changes along a field extension
`L/F`, the base change map `β_{i ≫ g}(M)` is invertible if `β_g(M)` is
(`ProEtale.CondensedRing.isIso_upperShriekBaseChangeOfMap_app_of_fieldExtension`). -/
theorem isIso_upperShriekBaseChangeOfMap_comp_app_of_fieldExtension
    (hY : IsPullback πY Y'.hom Y.hom (Spec.map (CommRingCat.ofHom (algebraMap F L))))
    (sqi : IsPullback πZ i'.left i.left πY) (sqg : IsPullback πY g'.left g.left πP)
    (sqig : IsPullback πZ (i' ≫ g').left (i ≫ g).left πP)
    (M : Dᵇc(P.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    [IsIso ((upperShriekBaseChangeOfMap ℓ sqg).app M)] :
    IsIso ((upperShriekBaseChangeOfMap ℓ sqig).app M) :=
  have := isIso_upperShriekBaseChangeOfMap_app_of_fieldExtension ℓ hY sqi
    ((boundedConstructibleUpperShriek ℓ g).obj M)
  isIso_upperShriekBaseChangeOfMap_comp_app ℓ sqi sqg sqig M

end FieldExtension

end AlgebraicGeometry.ProEtale.CondensedRing
