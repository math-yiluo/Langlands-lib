/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSliceIntegral
public import WeilConjectures.TraceFormula.Specialization.NearbyFinitenessSlice
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethSlice
public import WeilConjectures.SixFunctors.NearbyCycles.KunnethGeneric
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeSplitMono

/-!

# Factorisation of the geometric slice through a generic slice trait

Let `M` be a model of finite type over `S = Spec k'⟦t⟧` along `q`, with a coordinate
`b : 𝒳 ⟶ 𝔸¹_S` (`b ≫ (𝔸¹_S ⟶ S) = q`), let `K = k'(x)^alg` and let
`M'' = M.baseChange hM b hb (traitSlice x)` be the geometric slice of `M` along `b`, over the trait
`Spec K⟦t⟧`, with its morphism of models `M'' ⟶ M` (`NearbyCyclesModel.baseChangeHom`). Following
Deligne (SGA 4½, [Th. finitude], 3.3–3.4), the generic slice `Spec K⟦t⟧ ⟶ 𝔸¹_S` factors through a
generic slice trait `S' = Spec R` of `𝔸¹_S` (`AlgebraicGeometry.GenericSliceTrait`), weakly étale
over `𝔸¹_S`, and with `X' = 𝒳 ×_{𝔸¹_S} S'` the morphism of models of the geometric generic
fibres factors as
```
(M'' over Spec K⟦t⟧) ──τ──→ (X' over S') ──σ──→ (𝒳 over S)
```
* `τ` (`NearbyCyclesModel.coordinateSliceTraitChangeHom`) is the change of strictly henselian
  trait `Spec K⟦t⟧ ⟶ S'`, with cartesian square of total spaces
  (`NearbyCyclesModel.isPullback_coordinateSliceTraitChangeTotal`);
* `σ` (`NearbyCyclesModel.coordinateSliceTraitHom`) is the slice of `M` over the slice trait
  `S' ⟶ S` (`NearbyCyclesModel.sliceTraitHom`), with weakly étale morphism of total spaces.

This generalises `NearbyCyclesModel.genericSliceTraitChangeHom` and
`NearbyCyclesModel.genericSliceTraitHom` from the coordinates of `𝔸ⁿ⁺¹_S` to a general model with a
coordinate. As `M'' ⟶ M` keeps the identification `ε` of `M`, while the slice over `S'` is a
geometric model (`ε = j`, `NearbyCyclesModel.sliceTraitHom`), `τ` and `σ` are defined directly
on the models of the geometric generic fibres (`NearbyCyclesModel.toGeneric`, with `ε = 𝟙`), in
terms of the generic slice trait `D` itself (going through `GenericSliceTrait.toSliceTrait` in
statements makes them very slow to check). The pullback exchange of a morphism of models is a
split monomorphism once that of its geometric generic part is
(`NearbyCyclesModel.Hom.isSplitMono_pullbackExchange_app_of_toGeneric`), and the pullback
exchange of `M'' ⟶ M` is split as soon as that of `τ` is invertible and that of `σ` is split
(`isSplitMono_pullbackExchange_baseChangeHom_traitSlice_of_coordinateSliceTrait`),
for any coefficients.

The pullback exchange of `τ` with `𝒪_E`-coefficients is invertible by the invariance of nearby
cycles under change of trait
(`NearbyCyclesModel.isIso_pullbackExchange_coordinateSliceTraitChangeHom_padicIntegers`).

-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel.Hom

section Abstract

/-- The converse of the split pullback exchange criterion, in abstract categories: with `θi`, `θε`
invertible, if `α` is a split monomorphism at `o`, so is `IM` of the base change morphism `β'` at
`E_N o`; `β` is given together with `β'` and a proof of `β' = β`. -/
private lemma isSplitMono_map_app_of_isSplitMono_pullbackExchange_app_aux
    {DY' DX' DTN DTM DGN DGM DY DX : Type*} [Category DY'] [Category DX'] [Category DTN]
    [Category DTM] [Category DGN] [Category DGM] [Category DY] [Category DX]
    {Fp' : DY' ⥤ DX'} {IN : DTN ⥤ DY'} {IM : DTM ⥤ DX'} {T : DTN ⥤ DTM}
    {JNs : DGN ⥤ DTN} {JMs : DGM ⥤ DTM} {G : DGN ⥤ DGM} {EN : DY ⥤ DGN} {EM : DX ⥤ DGM}
    {F : DY ⥤ DX} (θi : IN ⋙ Fp' ⟶ T ⋙ IM) [IsIso θi] (β β' : JNs ⋙ T ⟶ G ⋙ JMs)
    (h : β' = β) (θε : EN ⋙ G ⟶ F ⋙ EM) [IsIso θε]
    (α : (EN ⋙ JNs ⋙ IN) ⋙ Fp' ⟶ F ⋙ EM ⋙ JMs ⋙ IM)
    (hα : α = Functor.whiskerLeft (EN ⋙ JNs) θi ≫
      Functor.whiskerRight (Functor.whiskerLeft EN β ≫ Functor.whiskerRight θε JMs) IM)
    (o : DY) (hα' : IsSplitMono (α.app o)) : IsSplitMono (IM.map (β'.app (EN.obj o))) := by
  subst h hα
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp] at hα'
  have e : IM.map (β'.app (EN.obj o)) = inv (θi.app ((EN ⋙ JNs).obj o)) ≫
      (θi.app ((EN ⋙ JNs).obj o) ≫ IM.map (β'.app (EN.obj o)) ≫
        IM.map (JMs.map (θε.app o))) ≫ inv (IM.map (JMs.map (θε.app o))) := by
    simp
  rw [e]
  infer_instance

/-- Split monomorphisms of `H` applied to a natural transformation are transported along
isomorphisms of objects. -/
private lemma isSplitMono_map_app_of_iso {C D E : Type*} [Category C] [Category D] [Category E]
    {F G : C ⥤ D} (η : F ⟶ G) (H : D ⥤ E) {o o' : C} (e : o ≅ o')
    (h : IsSplitMono (H.map (η.app o))) : IsSplitMono (H.map (η.app o')) :=
  NatTrans.isSplitMono_app_of_iso (Functor.whiskerRight η H) e.symm h

/-- Split pullback exchanges from those of the models of the geometric generic fibres, in
abstract categories: with `θi`, `θε`, `θε'` invertible and `E'_N ≅ 𝟭`, the exchange `α` built
from `E_N` is a split monomorphism at `o` if the exchange `α'` built from `E'_N`, with the same
`θi` and base change morphism `m`, is one at `E_N o`. -/
private lemma isSplitMono_pullbackExchange_app_of_toGeneric_aux
    {DY' DX' DTN DTM DGN DGM DY DX : Type*} [Category DY'] [Category DX'] [Category DTN]
    [Category DTM] [Category DGN] [Category DGM] [Category DY] [Category DX]
    {Fp' : DY' ⥤ DX'} {IN : DTN ⥤ DY'} {IM : DTM ⥤ DX'} {T : DTN ⥤ DTM}
    {JNs : DGN ⥤ DTN} {JMs : DGM ⥤ DTM} {G : DGN ⥤ DGM} {EN : DY ⥤ DGN} {EM : DX ⥤ DGM}
    {F : DY ⥤ DX} {EN' : DGN ⥤ DGN} {EM' : DGM ⥤ DGM}
    (θi : IN ⋙ Fp' ⟶ T ⋙ IM) [IsIso θi] (m : JNs ⋙ T ⟶ G ⋙ JMs)
    (θε : EN ⋙ G ⟶ F ⋙ EM) [IsIso θε] (θε' : EN' ⋙ G ⟶ G ⋙ EM') [IsIso θε']
    (eN : EN' ≅ 𝟭 DGN)
    (α : (EN ⋙ JNs ⋙ IN) ⋙ Fp' ⟶ F ⋙ EM ⋙ JMs ⋙ IM)
    (hα : α = Functor.whiskerLeft (EN ⋙ JNs) θi ≫
      Functor.whiskerRight (Functor.whiskerLeft EN m ≫ Functor.whiskerRight θε JMs) IM)
    (α' : (EN' ⋙ JNs ⋙ IN) ⋙ Fp' ⟶ G ⋙ EM' ⋙ JMs ⋙ IM)
    (hα' : α' = Functor.whiskerLeft (EN' ⋙ JNs) θi ≫
      Functor.whiskerRight (Functor.whiskerLeft EN' m ≫ Functor.whiskerRight θε' JMs) IM)
    (o : DY) (h : IsSplitMono (α'.app (EN.obj o))) : IsSplitMono (α.app o) := by
  subst hα hα'
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp] at h ⊢
  have e : IM.map (m.app (EN'.obj (EN.obj o))) = inv (θi.app ((EN' ⋙ JNs).obj (EN.obj o))) ≫
      (θi.app ((EN' ⋙ JNs).obj (EN.obj o)) ≫ IM.map (m.app (EN'.obj (EN.obj o))) ≫
        IM.map (JMs.map (θε'.app (EN.obj o)))) ≫ inv (IM.map (JMs.map (θε'.app (EN.obj o)))) := by
    simp
  have hm : IsSplitMono (IM.map (m.app (EN'.obj (EN.obj o)))) := by
    rw [e]
    infer_instance
  have : IsSplitMono (IM.map (m.app (EN.obj o))) :=
    isSplitMono_map_app_of_iso m IM (eN.app (EN.obj o)) hm
  infer_instance

end Abstract

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X X' Y Y' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {f : X ⟶ Y} {f' : X' ⟶ Y'}

/-- **The restricted base change morphism from a split pullback exchange**: if the pullback
exchange `α_f` of a morphism of models is a split monomorphism at `K`, then so is the base change
morphism `Lt^* Rj_{N*} ⟶ Rj_{M*} Lg^*` of the square of geometric generic fibres, restricted to the
special fibre by `Li_M^*`, at `Lε_N^* K`. -/
theorem isSplitMono_map_exchangeRight_app_of_isSplitMono_pullbackExchange_app (φ : M.Hom N f f')
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (hK : IsSplitMono ((φ.pullbackExchange Λ).app K)) :
    IsSplitMono ((L((M.i)^*⟦Λ⟧)).map ((Adjunction.exchangeRight
      (derivedUpperStarLowerStarAdjunction Λ N.j) (derivedUpperStarLowerStarAdjunction Λ M.j)
      (pullbackSquareComparison Λ φ.commSq_j)).app ((L((N.ε)^*⟦Λ⟧)).obj K))) :=
  isSplitMono_map_app_of_isSplitMono_pullbackExchange_app_aux
    (pullbackSquareComparison Λ φ.commSq_i).hom
    (mateEquiv (derivedUpperStarLowerStarAdjunction Λ N.j)
      (derivedUpperStarLowerStarAdjunction Λ M.j)
      (pullbackSquareComparison Λ φ.commSq_j).hom)
    _ ((baseChangeMap_eq_exchangeRight Λ φ.commSq_j).symm.trans
      (φ.baseChangeMap_commSq_j_eq_mateEquiv Λ))
    (pullbackSquareComparison Λ φ.commSq_ε).hom (φ.pullbackExchange Λ) rfl K hK

/-- **Reduction of split pullback exchanges to the geometric generic fibres**: the pullback
exchange `α_f` of a morphism of models `φ` is a split monomorphism at `K` if the pullback
exchange of the morphism `φ.toGeneric` of the models of the geometric generic fibres is one at
`Lε_N^* K`. Both are, up to isomorphisms, the base change morphism of `Rj_*` restricted to the
special fibre of `M`, at `Lε_N^* K`. -/
theorem isSplitMono_pullbackExchange_app_of_toGeneric (φ : M.Hom N f f')
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (h : IsSplitMono ((φ.toGeneric.pullbackExchange Λ).app ((L((N.ε)^*⟦Λ⟧)).obj K))) :
    IsSplitMono ((φ.pullbackExchange Λ).app K) :=
  isSplitMono_pullbackExchange_app_of_toGeneric_aux (pullbackSquareComparison Λ φ.commSq_i).hom
    (mateEquiv (derivedUpperStarLowerStarAdjunction Λ N.j)
      (derivedUpperStarLowerStarAdjunction Λ M.j)
      (pullbackSquareComparison Λ φ.commSq_j).hom)
    (pullbackSquareComparison Λ φ.commSq_ε).hom
    (pullbackSquareComparison Λ φ.toGeneric.commSq_ε).hom (leftDerivedUpperStarId Λ N.generic)
    (φ.pullbackExchange Λ) rfl (φ.toGeneric.pullbackExchange Λ) rfl K h

end NearbyCyclesModel.Hom

namespace NearbyCyclesModel

variable {k' : Type u} [Field k'] {X : Scheme.{u}} {X' : Over (Spec (.of k'))}
  {M : NearbyCyclesModel X X'.left} {q : M.total ⟶ trait k'}
  {g : M.generic ⟶ Spec (.of (traitGenericField k'))} (hM : M.IsTraitModelOver q g)
  (b : M.total ⟶ 𝔸(ULift.{u} (Fin 1); trait k'))
  (hb : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q) (D : GenericSliceTrait k')

/-! ### The slice over the generic slice trait -/

/-- The **model of the slice over a generic slice trait**, on its geometric generic fibre: total
space `X' = 𝒳 ×_{𝔸¹_S} S'` (along the coordinate `b`), geometric generic fibre `X' ×_{S'} Spec Ω'`,
special fibre `X' ×_{S'} Spec κ'` and `ε = 𝟙`. It is the model of the geometric generic fibre
(`NearbyCyclesModel.toGeneric`) of `NearbyCyclesModel.sliceTraitModel`, written directly in
terms of the generic slice trait `D`. -/
@[simps]
noncomputable def coordinateSliceTraitModel :
    NearbyCyclesModel (pullback (pullback.snd b D.toAffineLine) (Spec.map (CommRingCat.ofHom D.a)))
      (pullback (pullback.snd b D.toAffineLine) (Spec.map (CommRingCat.ofHom D.b))) where
  total := pullback b D.toAffineLine
  generic := pullback (pullback.snd b D.toAffineLine) (Spec.map (CommRingCat.ofHom D.a))
  j := pullback.fst _ _
  i := pullback.fst _ _
  ε := 𝟙 _

/-- The structure morphism of `𝒳` and the projection `X' = 𝒳 ×_{𝔸¹_S} S' ⟶ S'` agree on `X'`. -/
@[reassoc]
lemma coordinateSliceTrait_fst_comp {q' : M.total ⟶ trait k'}
    (hb' : b ≫ 𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' = q') :
    pullback.fst b D.toAffineLine ≫ q' =
      pullback.snd b D.toAffineLine ≫ D.toAffineLine ≫
        𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k' := by
  rw [← hb', pullback.condition_assoc]

/-- The map `X' ×_{S'} Spec Ω' ⟶ 𝒳_η̄` of geometric generic fibres of the slice over the generic
slice trait. -/
noncomputable def coordinateSliceTraitGeneric :
    pullback (pullback.snd b D.toAffineLine) (Spec.map (CommRingCat.ofHom D.a)) ⟶ M.generic :=
  hM.isPullback_j.lift (pullback.fst _ _ ≫ pullback.fst _ _)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom D.ωS)) (by
      rw [Category.assoc, coordinateSliceTrait_fst_comp b D hb, pullback.condition_assoc,
        D.generic_over, Category.assoc])

/-- The map `X' ×_{S'} Spec κ' ⟶ 𝒳_s` of special fibres of the slice over the generic slice
trait. -/
noncomputable def coordinateSliceTraitSpecial :
    pullback (pullback.snd b D.toAffineLine) (Spec.map (CommRingCat.ofHom D.b)) ⟶ X'.left :=
  hM.isPullback_i.lift (pullback.fst _ _ ≫ pullback.fst _ _)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom D.κS)) (by
      rw [Category.assoc, coordinateSliceTrait_fst_comp b D hb, pullback.condition_assoc,
        D.closed_over, Category.assoc])

/-- The **slice of a model over a generic slice trait** `σ`, on the models of the geometric
generic fibres: from the model of `X' = 𝒳 ×_{𝔸¹_S} S'` over the generic slice trait `S'` to the
model of the geometric generic fibre of `M`, along the coordinate `b`; it is
`NearbyCyclesModel.sliceTraitHom` read on the geometric generic fibres. Its morphism of total
spaces `X' ⟶ 𝒳` is weakly étale. -/
@[simps]
noncomputable def coordinateSliceTraitHom :
    (coordinateSliceTraitModel b D).Hom M.toGeneric (coordinateSliceTraitGeneric hM b hb D)
      (coordinateSliceTraitSpecial hM b hb D) where
  total := pullback.fst b D.toAffineLine
  generic := coordinateSliceTraitGeneric hM b hb D
  comm_j := hM.isPullback_j.lift_fst _ _ _
  comm_i := hM.isPullback_i.lift_fst _ _ _
  comm_ε := (Category.comp_id _).trans (Category.id_comp _).symm

instance : WeaklyEtale (coordinateSliceTraitHom hM b hb D).total :=
  MorphismProperty.of_isPullback (P := @WeaklyEtale) (IsPullback.of_hasPullback _ _).flip
    D.weaklyEtale

/-! ### The change of trait to the generic slice trait -/

/-- The morphism `𝒳 ×_{𝔸¹_S} Spec K⟦t⟧ ⟶ 𝒳 ×_{𝔸¹_S} S'` of total spaces induced by the
factorisation of the generic slice through the generic slice trait. -/
noncomputable def coordinateSliceTraitChangeTotal :
    pullback b (traitSlice (traitSliceCoord k')) ⟶ pullback b D.toAffineLine :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom D.ι)) (by
    rw [pullback.condition, Category.assoc]
    exact congrArg (pullback.snd _ _ ≫ ·) D.spec_ι_comp.symm)

@[reassoc (attr := simp)]
lemma coordinateSliceTraitChangeTotal_fst :
    coordinateSliceTraitChangeTotal b D ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma coordinateSliceTraitChangeTotal_snd :
    coordinateSliceTraitChangeTotal b D ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom D.ι) :=
  pullback.lift_snd _ _ _

/-- The square of total spaces of the change of trait `Spec K⟦t⟧ ⟶ S'` is cartesian:
`𝒳 ×_{𝔸¹_S} Spec K⟦t⟧ = (𝒳 ×_{𝔸¹_S} S') ×_{S'} Spec K⟦t⟧`. -/
lemma isPullback_coordinateSliceTraitChangeTotal :
    IsPullback (coordinateSliceTraitChangeTotal b D) (pullback.snd _ _)
      (pullback.snd b D.toAffineLine) (Spec.map (CommRingCat.ofHom D.ι)) := by
  refine IsPullback.of_right ?_ (coordinateSliceTraitChangeTotal_snd b D)
    (IsPullback.of_hasPullback b D.toAffineLine)
  rw [coordinateSliceTraitChangeTotal_fst]
  convert IsPullback.of_hasPullback b (traitSlice (traitSliceCoord k')) using 1
  exact D.spec_ι_comp

/-- The map `(𝒳 ×_{𝔸¹_S} Spec K⟦t⟧) ×_{K⟦t⟧} Spec Ω_K ⟶ X' ×_{S'} Spec Ω'` of geometric generic
fibres. -/
noncomputable def coordinateSliceTraitChangeGeneric :
    pullback (pullback.snd b (traitSlice (traitSliceCoord k')))
        (traitGenericPoint (traitSliceField k')) ⟶
      pullback (pullback.snd b D.toAffineLine) (Spec.map (CommRingCat.ofHom D.a)) :=
  pullback.lift (pullback.fst _ _ ≫ coordinateSliceTraitChangeTotal b D)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom D.ωK)) (by
      rw [Category.assoc, coordinateSliceTraitChangeTotal_snd, pullback.condition_assoc,
        Category.assoc]
      congr 1
      simp only [traitGenericPoint, ← Spec.map_comp, ← CommRingCat.ofHom_comp, D.ωK_comp_a])

/-- The map `(𝒳 ×_{𝔸¹_S} Spec K⟦t⟧) ×_{K⟦t⟧} Spec K ⟶ X' ×_{S'} Spec κ'` of special fibres. -/
noncomputable def coordinateSliceTraitChangeSpecial :
    pullback (pullback.snd b (traitSlice (traitSliceCoord k')))
        (traitClosedPoint (traitSliceField k')) ⟶
      pullback (pullback.snd b D.toAffineLine) (Spec.map (CommRingCat.ofHom D.b)) :=
  pullback.lift (pullback.fst _ _ ≫ coordinateSliceTraitChangeTotal b D)
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom D.κK)) (by
      rw [Category.assoc, coordinateSliceTraitChangeTotal_snd, pullback.condition_assoc,
        Category.assoc]
      congr 1
      simp only [traitClosedPoint, ← Spec.map_comp, ← CommRingCat.ofHom_comp, D.κK_comp_b])

/-- The **change of trait to the generic slice trait** `τ`, on the models of the geometric generic
fibres: from the model of the geometric generic fibre of the geometric slice
`𝒳 ×_{𝔸¹_S} Spec K⟦t⟧` over `Spec K⟦t⟧` to that of `X' = 𝒳 ×_{𝔸¹_S} S'` over the generic slice
trait `S'`, along the morphism of strictly henselian traits `Spec K⟦t⟧ ⟶ S'`. -/
@[simps]
noncomputable def coordinateSliceTraitChangeHom :
    (baseChange hM b hb (traitSlice (traitSliceCoord k'))
        (traitSlice_over (traitSliceCoord k'))).toGeneric.Hom
      (coordinateSliceTraitModel b D) (coordinateSliceTraitChangeGeneric b D)
      (coordinateSliceTraitChangeSpecial b D) where
  total := coordinateSliceTraitChangeTotal b D
  generic := coordinateSliceTraitChangeGeneric b D
  comm_j := pullback.lift_fst _ _ _
  comm_i := pullback.lift_fst _ _ _
  comm_ε := (Category.comp_id _).trans (Category.id_comp _).symm

/-- The composite `τ ≫ σ` has the morphism of total spaces of the geometric slice. -/
lemma coordinateSliceTraitChangeHom_total_comp :
    (coordinateSliceTraitChangeHom hM b hb D).total ≫ (coordinateSliceTraitHom hM b hb D).total =
      (baseChangeHom hM b hb (traitSlice (traitSliceCoord k'))
        (traitSlice_over (traitSliceCoord k'))).toGeneric.total :=
  coordinateSliceTraitChangeTotal_fst b D

/-- The composite `τ ≫ σ` has the morphism of geometric generic fibres of the geometric slice. -/
lemma coordinateSliceTraitChangeGeneric_comp :
    coordinateSliceTraitChangeGeneric b D ≫ coordinateSliceTraitGeneric hM b hb D =
      (baseChangeHom hM b hb (traitSlice (traitSliceCoord k'))
        (traitSlice_over (traitSliceCoord k'))).generic := by
  refine hM.isPullback_j.hom_ext ?_ ?_
  · simp [coordinateSliceTraitChangeGeneric, coordinateSliceTraitGeneric]
  · simp only [coordinateSliceTraitGeneric, coordinateSliceTraitChangeGeneric, Category.assoc,
      IsPullback.lift_snd, pullback.lift_snd_assoc, baseChangeHom_generic, baseChangeGenericMap_g]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, D.ωK_comp_ωS]
    rfl

/-- The composite `τ ≫ σ` has the morphism of geometric generic fibres of the geometric slice,
in terms of the morphisms of models. -/
lemma coordinateSliceTraitChangeHom_generic_comp :
    (coordinateSliceTraitChangeHom hM b hb D).generic ≫
        (coordinateSliceTraitHom hM b hb D).generic =
      (baseChangeHom hM b hb (traitSlice (traitSliceCoord k'))
        (traitSlice_over (traitSliceCoord k'))).toGeneric.generic :=
  coordinateSliceTraitChangeGeneric_comp hM b hb D

/-- The composite `τ ≫ σ` has the morphism of special fibres of the geometric slice. -/
lemma coordinateSliceTraitChangeSpecial_comp :
    coordinateSliceTraitChangeSpecial b D ≫ coordinateSliceTraitSpecial hM b hb D =
      baseChangeSpecialMap hM b hb (traitSlice (traitSliceCoord k'))
        (traitSlice_over (traitSliceCoord k')) := by
  refine hM.isPullback_i.hom_ext ?_ ?_
  · simp [coordinateSliceTraitChangeSpecial, coordinateSliceTraitSpecial]
  · simp only [coordinateSliceTraitSpecial, coordinateSliceTraitChangeSpecial, Category.assoc,
      IsPullback.lift_snd, pullback.lift_snd_assoc, baseChangeSpecialMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, D.κK_comp_κS]

/-! ### The factorisation of the pullback exchange -/

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **The pullback exchange of the geometric slice through the generic slice trait**: the
pullback exchange of the morphism of models `M'' ⟶ M` from the geometric slice of `M` along the
coordinate `b` is a split monomorphism at `A` as soon as, on the models of the geometric generic
fibres, the pullback exchange of the change of trait `τ` is invertible at `Lσ^* (Lε^* A)` and that
of the slice `σ` over the generic slice trait is a split monomorphism at `Lε^* A`. This holds for
any coefficients `Λ`. -/
theorem isSplitMono_pullbackExchange_baseChangeHom_traitSlice_of_coordinateSliceTrait
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (h₁ : IsIso (((coordinateSliceTraitChangeHom hM b hb D).pullbackExchange Λ).app
      ((L((coordinateSliceTraitGeneric hM b hb D)^*⟦Λ⟧)).obj ((L((M.ε)^*⟦Λ⟧)).obj A))))
    (h₂ : IsSplitMono (((coordinateSliceTraitHom hM b hb D).pullbackExchange Λ).app
      ((L((M.ε)^*⟦Λ⟧)).obj A))) :
    IsSplitMono (((baseChangeHom hM b hb (traitSlice (traitSliceCoord k'))
      (traitSlice_over (traitSliceCoord k'))).pullbackExchange Λ).app A) := by
  have key := Hom.isSplitMono_pullbackExchange_app_of_comp Λ
    (coordinateSliceTraitChangeHom hM b hb D) (coordinateSliceTraitHom hM b hb D)
    (baseChangeHom hM b hb (traitSlice (traitSliceCoord k'))
      (traitSlice_over (traitSliceCoord k'))).toGeneric
    (coordinateSliceTraitChangeGeneric_comp hM b hb D)
    (coordinateSliceTraitChangeSpecial_comp hM b hb D)
    (coordinateSliceTraitChangeHom_total_comp hM b hb D)
    (coordinateSliceTraitChangeHom_generic_comp hM b hb D) ((L((M.ε)^*⟦Λ⟧)).obj A) h₁ h₂
  exact Hom.isSplitMono_pullbackExchange_app_of_toGeneric Λ
    (baseChangeHom hM b hb (traitSlice (traitSliceCoord k'))
      (traitSlice_over (traitSliceCoord k'))) A key

/-! ### The change of trait with `𝒪_E`-coefficients -/

variable {ℓ : ℕ} [Fact ℓ.Prime] [Fact (ringChar k' ≠ ℓ)]

/-- **Change of trait to the generic slice trait, `𝒪_E`-coefficients** (SGA 4½, [Th. finitude],
3.7): on the models of the geometric generic fibres, the pullback exchange of the change of
strictly henselian trait `τ : (𝒳 ×_{𝔸¹_S} Spec K⟦t⟧ over Spec K⟦t⟧) ⟶ (X' over S')` with
`𝒪_E`-coefficients is an isomorphism at every bounded constructible complex on the geometric
generic fibre of `X'`; a case of
`NearbyCyclesModel.Hom.isIso_pullbackExchange_app_of_isPullback_trait_padicIntegers`. -/
theorem isIso_pullbackExchange_coordinateSliceTraitChangeHom_padicIntegers
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {B₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology
      (pullback (pullback.snd b D.toAffineLine) (Spec.map (CommRingCat.ofHom D.a)))) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1)
        (pullback (pullback.snd b D.toAffineLine) (Spec.map (CommRingCat.ofHom D.a)))))}
    (hB₀ : boundedConstructible _ B₀) :
    IsIso (((coordinateSliceTraitChangeHom hM b hb D).pullbackExchange
      (Profinite.padicIntegersRingObj ℓ E.1)).app B₀) := by
  have : Fact (ringChar D.κ ≠ ℓ) := ⟨D.ringChar_κ ▸ Fact.out⟩
  have := hM.locallyOfFiniteType
  have := hM.quasiCompact
  have := hM.isSeparated
  have : LocallyOfFiniteType b := by
    subst hb
    exact locallyOfFiniteType_of_comp b (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k')
  have : QuasiCompact b := by
    subst hb
    exact QuasiCompact.of_comp b (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k')
  have : IsSeparated b := by
    subst hb
    exact IsSeparated.of_comp b (𝔸(ULift.{u} (Fin 1); trait k') ↘ trait k')
  have hB₀' := boundedConstructible_leftDerivedUpperStar_obj_of_scheme _ (𝟙 _) _ hB₀
  exact Hom.isIso_pullbackExchange_app_of_isPullback_trait_padicIntegers (ι := D.ι) (a₁ := D.a)
    (a₂ := algebraMap _ _) (c := D.ωK) (b₁ := D.b) (b₂ := PowerSeries.constantCoeff)
    D.injective_ι D.maximalIdeal_eq_map_ι D.injective_a
    (algebraMap_traitGenericField_injective _) D.isAlgebraic_a
    (isAlgebraic_traitGenericField _) D.ωK_comp_a D.ker_b
    PowerSeries.ker_coeff_eq_max_ideal (coordinateSliceTraitChangeHom hM b hb D)
    (pullback.snd b D.toAffineLine) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
    (pullback.snd _ _) (IsPullback.of_hasPullback _ _) (pullback.snd _ _) (pullback.snd _ _)
    (IsPullback.of_hasPullback _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
    (isPullback_coordinateSliceTraitChangeTotal b D) (pullback.lift_snd _ _ _) E hB₀'

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
