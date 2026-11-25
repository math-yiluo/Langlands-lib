/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.CoproductSections
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!

# Pro-étale sheaves on a finite disjoint union

Let `Z` be the disjoint union of finitely many schemes `T i`, through the open immersions
`f i : T i ⟶ Z`. A pro-étale sheaf `G` on `Z` is the product of the pushforwards
`(f i)_* (f i)^* G` of its restrictions, the projections being the units of the adjunctions
`(f i)^* ⊣ (f i)_*` (`AlgebraicGeometry.ProEtale.isLimitFanUnitOfIsColimitCofan`).

Along the weakly étale `f i`, the pullback is the restriction along the localization functor
(`AlgebraicGeometry.ProEtale.upperStarIsoLocalizationRestriction`), so on sections over an
object `W` of `Z_proét` the unit is the restriction of sections along `W ×_Z T i ⟶ W`. The
`W ×_Z T i` exhibit `W` as their disjoint union, coproducts of schemes being universal, so the
claim is the sheaf condition for this disjoint covering family
(`AlgebraicGeometry.ProEtale.isLimitSectionsFanOfIsColimitCofan`).

-/

@[expose] public section

universe u' u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Limits

/-- A fan whose legs are those of a limit fan followed by isomorphisms is a limit fan. -/
noncomputable def Fan.isLimitMkCompOfIsIso {C : Type*} [Category C] {ι : Type*} {X : C}
    {Y Y' : ι → C} {π : ∀ i, X ⟶ Y i} (h : IsLimit (Fan.mk X π)) (e : ∀ i, Y i ⟶ Y' i)
    [∀ i, IsIso (e i)] : IsLimit (Fan.mk X fun i ↦ π i ≫ e i) :=
  Fan.IsLimit.mk _ (fun s ↦ Fan.IsLimit.lift h fun i ↦ s.proj i ≫ inv (e i))
    (fun s i ↦ by
      change _ ≫ π i ≫ e i = _
      rw [← Category.assoc]
      erw [Fan.IsLimit.fac h]
      simp)
    (fun s m hm ↦ Fan.IsLimit.hom_ext h _ _ fun i ↦ by
      rw [Fan.IsLimit.fac h, ← hm i]
      simp)

/-- A fan is a limit if its image under a functor reflecting limits of its shape is, up to
isomorphisms of the legs, a limit fan. -/
noncomputable def Fan.isLimitOfIsLimitMapComp {C D : Type*} [Category C] [Category D] {ι : Type*}
    (F : C ⥤ D) [ReflectsLimitsOfShape (Discrete ι) F] {M : C} {Y : ι → C} (π : ∀ i, M ⟶ Y i)
    {Y' : ι → D} (π' : ∀ i, F.obj M ⟶ Y' i) (h : IsLimit (Fan.mk (F.obj M) π'))
    (e : ∀ i, Y' i ⟶ F.obj (Y i)) [∀ i, IsIso (e i)] (he : ∀ i, π' i ≫ e i = F.map (π i)) :
    IsLimit (Fan.mk M π) :=
  isLimitOfReflects F ((isLimitMapConeFanMkEquiv F Y π).symm
    (IsLimit.ofIsoLimit (r := Fan.mk (F.obj M) fun i ↦ π' i ≫ e i)
      (t := Fan.mk (F.obj M) fun i ↦ F.map (π i)) (Fan.isLimitMkCompOfIsIso h e)
      (Cone.ext (Iso.refl _) fun ⟨i⟩ ↦ (he i).trans (Category.id_comp _).symm)))

end CategoryTheory.Limits

namespace AlgebraicGeometry

open Scheme ProEtale

/-- The base change of a finite coproduct decomposition of schemes is a coproduct
decomposition, coproducts of schemes being universal. -/
noncomputable def Scheme.isColimitCofanPullbackFst {ι : Type*} [Finite ι] {Z W : Scheme.{u}}
    {T : ι → Scheme.{u}} {f : ∀ i, T i ⟶ Z} (hf : IsColimit (Cofan.mk Z f)) (w : W ⟶ Z) :
    IsColimit (Cofan.mk W fun i ↦ pullback.fst w (f i)) :=
  (FinitaryPreExtensive.isUniversal_finiteCoproducts hf (Cofan.mk W fun i ↦ pullback.fst w (f i))
    (Discrete.natTrans fun i ↦ pullback.snd w (f i.as)) w
    (by ext ⟨i⟩; exact pullback.condition.symm) (NatTrans.Equifibered.of_discrete _)
    (fun ⟨i⟩ ↦ IsPullback.of_hasPullback w (f i))).some

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- **Pro-étale sheaves on a finite disjoint union**: if `f i : T i ⟶ Z` exhibit `Z` as the
disjoint union of finitely many schemes `T i`, a pro-étale sheaf `G` on `Z` is the product of
the `(f i)_* (f i)^* G`, with the units of `(f i)^* ⊣ (f i)_*` as projections. -/
noncomputable def ProEtale.isLimitFanUnitOfIsColimitCofan {ι : Type u} [Finite ι] {Z : Scheme.{u}}
    {T : ι → Scheme.{u}} {f : ∀ i, T i ⟶ Z} (hf : IsColimit (Cofan.mk Z f))
    (G : Sheaf (ProEt.topology Z) A) :
    IsLimit (Fan.mk G fun i ↦ (ProEtale.upperStarLowerStarAdjunction A (f i)).unit.app G) := by
  have hwe (i : ι) : WeaklyEtale (f i) := by
    have := Scheme.isOpenImmersion_of_isColimit_cofan hf i
    infer_instance
  have hu (i : ι) := (ProEtale.upperStarLowerStarAdjunction A (f i)).unit_leftAdjointUniq_hom_app
    (ProEtale.localizationRestrictionLowerStarAdjunction A (f i) (hwe i)) G
  have H : IsLimit (Fan.mk G fun i ↦
      (ProEtale.localizationRestrictionLowerStarAdjunction A (f i) (hwe i)).unit.app G) := by
    apply isLimitOfReflects (sheafToPresheaf _ A)
    refine (isLimitMapConeFanMkEquiv (sheafToPresheaf _ A) _ _).symm ?_
    apply evaluationJointlyReflectsLimits
    intro W
    refine (isLimitMapConeFanMkEquiv ((evaluation _ A).obj W) _ _).symm ?_
    refine IsLimit.ofIsoLimit (ProEtale.isLimitSectionsFanOfIsColimitCofan G
      (fun i ↦ (MorphismProperty.Over.mapPullbackAdj _ ⊤ (f i) (hwe i) trivial).counit.app W.unop)
      (Scheme.isColimitCofanPullbackFst hf W.unop.hom))
      (Cone.ext (Iso.refl _) fun ⟨i⟩ ↦ ?_)
    simp [ProEtale.localizationRestrictionLowerStarAdjunction]
  refine IsLimit.ofIsoLimit (Fan.isLimitMkCompOfIsIso H fun i ↦
    (f i)_*[A].map ((ProEtale.upperStarIsoLocalizationRestriction A (f i) (hwe i)).inv.app G))
    (Cone.ext (Iso.refl _) fun ⟨i⟩ ↦ ?_)
  simp only [Fan.mk_pt, Fan.mk_π_app, Iso.refl_hom, Category.id_comp, ← hu, Category.assoc,
    ← Functor.map_comp]
  simp [ProEtale.upperStarIsoLocalizationRestriction]

end AlgebraicGeometry
