/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import WeilConjectures.Compactification.Dense
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedDirectImageOpenCoherence
import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionLocalizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange

/-!
# A single composition model on the localizing closure

Source: blueprint proposition-composition-base-change-rf-shriek--1, The composition isomorphism
(blueprint: lem-sfb-localizing-lower-shriek-composition-model).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem normalized_ext
    {C D T : Type*} [Category C] [Category D] [Category T]
    [Preadditive C] [Preadditive D] [Preadditive T] [HasBinaryBiproducts C]
    (F G : C ⥤ D) (R : D ⥤ T) [F.Additive] [G.Additive] [R.Additive]
    (H : C ⥤ T) (b : G ⋙ R ⟶ H) (a : F ⋙ R ⟶ H)
    (m : ∀ A, F.obj A ⟶ G.obj A)
    (hm : ∀ A, R.map (m A) ≫ b.app A = a.app A)
    (hu : ∀ A n, R.map n ≫ b.app A = a.app A → n = m A)
    {A B : C} (s t : F.obj A ⟶ G.obj B)
    (h : R.map s ≫ b.app B = R.map t ≫ b.app B) : s = t := by
  let v : F.obj (A ⊞ B) ⟶ G.obj (A ⊞ B) :=
    F.map biprod.fst ≫ (s - t) ≫ G.map biprod.inr
  have hv : R.map v ≫ b.app (A ⊞ B) = 0 := by
    dsimp [v]
    simp only [Functor.map_comp, Category.assoc]
    have hb := b.naturality (biprod.inr : B ⟶ A ⊞ B)
    dsimp only [Functor.comp_map] at hb
    rw [hb]
    simp only [Functor.map_sub, Preadditive.sub_comp,
      ← Category.assoc, h, sub_self, zero_comp, comp_zero]
  have heq : m (A ⊞ B) + v = m (A ⊞ B) := by
    apply hu
    rw [Functor.map_add, Preadditive.add_comp, hm, hv, add_zero]
  have hz : v = 0 := add_left_cancel (heq.trans (add_zero _).symm)
  have hx := congrArg (fun z ↦ F.map (biprod.inl : A ⟶ A ⊞ B) ≫ z ≫
    G.map (biprod.snd : A ⊞ B ⟶ B)) hz
  dsimp only [v] at hx
  simp only [← Category.assoc, ← Functor.map_comp, biprod.inl_fst] at hx
  simp only [Category.assoc, ← Functor.map_comp, biprod.inr_snd,
    comp_zero] at hx
  rw [F.map_id, G.map_id] at hx
  simp only [Category.id_comp, Category.comp_id, zero_comp] at hx
  exact sub_eq_zero.mp hx

private noncomputable def interchangeRestrictionNatTrans
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Ybar : Scheme.{u}}
    (p : X ⟶ Y) (i : Y ⟶ Ybar) [IsOpenImmersion i]
    (c : Compactification.BoundaryCompactification (p ≫ i)) :
    (lowerStar Λ c.obj.obj.g).rightDerivedFunctor ⋙
        (upperStar Λ i).mapDerivedCategory ⟶
      (upperStar Λ c.obj.obj.i).mapDerivedCategory ⋙
        (lowerStar Λ p).rightDerivedFunctor where
  app := compositionInterchangeRestriction Λ p i c
  naturality {B B'} v := by
    simp only [compositionInterchangeRestriction, Adjunction.homEquiv_unit,
      Functor.comp_map]
    let ap := (derivedUpperStarLowerStarAdjunction Λ p).ofNatIsoLeft
      (leftDerivedUpperStarIsoMapDerivedCategory Λ p)
    let ar := (derivedUpperStarLowerStarAdjunction Λ c.obj.obj.g).ofNatIsoLeft
      (leftDerivedUpperStarIsoMapDerivedCategory Λ c.obj.obj.g)
    let η := whiskerLeft ((lowerStar Λ c.obj.obj.g).rightDerivedFunctor ⋙
      (upperStar Λ i).mapDerivedCategory) ap.unit
    let δ := whiskerLeft (lowerStar Λ c.obj.obj.g).rightDerivedFunctor
        (compositionInterchangePullback Λ p i c).hom ≫
      whiskerRight ar.counit (upperStar Λ c.obj.obj.i).mapDerivedCategory
    have h := (η ≫ whiskerRight δ (lowerStar Λ p).rightDerivedFunctor).naturality v
    simpa only [η, δ, ap, ar, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.map_comp, Functor.comp_map, Functor.comp_obj,
      Functor.id_map, Category.assoc] using h

private theorem exists_interchangeNatTrans
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Ybar : Scheme.{u}}
    (p : X ⟶ Y) (i : Y ⟶ Ybar) [IsOpenImmersion i]
    (c : Compactification.BoundaryCompactification (p ≫ i))
    (h : ∀ A : DerivedCategory (CategoryTheory.Mod
        (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)),
      ∃ m, compositionInterchangeIsNormalized Λ p i c A m ∧
        ∀ m', compositionInterchangeIsNormalized Λ p i c A m' → m' = m) :
    ∃ τ : (lowerStar Λ p).rightDerivedFunctor ⋙
          (openImmersionLowerShriek Λ i).mapDerivedCategory ⟶
        (openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory ⋙
          (lowerStar Λ c.obj.obj.g).rightDerivedFunctor,
      ∀ A, compositionInterchangeIsNormalized Λ p i c A (τ.app A) := by
  classical
  choose m hm hu using h
  let P := (lowerStar Λ p).rightDerivedFunctor
  let U := (upperStar Λ i).mapDerivedCategory
  let J := (openImmersionLowerShriek Λ c.obj.obj.i).mapDerivedCategory
  let F := P ⋙ (openImmersionLowerShriek Λ i).mapDerivedCategory
  let G := J ⋙ (lowerStar Λ c.obj.obj.g).rightDerivedFunctor
  let H := J ⋙ (upperStar Λ c.obj.obj.i).mapDerivedCategory ⋙ P
  let b : G ⋙ U ⟶ H := whiskerLeft J (interchangeRestrictionNatTrans Λ p i c)
  let a : F ⋙ U ⟶ H :=
    whiskerLeft P (asIso (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i).unit).inv ≫
      whiskerRight (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ c.obj.obj.i).unit P
  have hm' : ∀ A, U.map (m A) ≫ b.app A = a.app A := by
    intro A
    apply (cancel_epi ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i).unit.app
      (P.obj A))).mp
    simpa [a, b, P, U, J, H, interchangeRestrictionNatTrans,
      compositionInterchangeIsNormalized, Adjunction.homEquiv_unit, Category.assoc] using hm A
  have hu' : ∀ A (n : F.obj A ⟶ G.obj A),
      U.map n ≫ b.app A = a.app A → n = m A := by
    intro A n hn
    apply hu A n
    dsimp only [compositionInterchangeIsNormalized]
    rw [Adjunction.homEquiv_unit]
    have hn' := congrArg (fun q ↦
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ i).unit.app (P.obj A) ≫ q) hn
    simpa [a, b, P, U, J, H, interchangeRestrictionNatTrans, Category.assoc] using hn'
  refine ⟨{ app := m, naturality := ?_ }, hm⟩
  intro A B v
  apply normalized_ext F G U H b a m hm' hu'
  simp only [Functor.map_comp, Category.assoc]
  have hb := b.naturality v
  dsimp only [Functor.comp_map] at hb
  rw [hb]
  simp only [← Category.assoc, hm']
  exact a.naturality v

/-- Some compactification triple admits the composition isomorphism in the ambient
unbounded derived category, with the source restricted to the localizing closure.
No refinement compatibility or preservation witness is part of this assertion.

Source: blueprint proposition-composition-base-change-rf-shriek--1, The composition isomorphism
(blueprint: lem-sfb-localizing-lower-shriek-composition-model).

Proof: take dense compactifications f = jp and g = iq by Nagata. Compactify pi as
ur with u dense. The proper maps r and q compose and the quasi-compact open maps
j and u compose, giving a compactification of fg. Extension by zero for j sends
the localizing closure into the closure on its target, by open-immersion preservation.
Proper/open interchange supplies its normalized map i! Rp* A to Rr* u! A for every
unbounded A, and makes it invertible on this closure. Its normalization is natural:
write the normalization as U(m) b = a using the invertible open unit.
For two arrows from F(A) to G(B) with equal normalized restrictions, insert their
difference as the off-diagonal block on A ⊞ B. Adding this block to the unique
normalized component contradicts uniqueness unless the block is zero. Taking
the two off-diagonal projections equates the original arrows. Naturality of a
and b now applies this cancellation to the two naturality composites. Thus at
A = j! K these maps form a natural isomorphism on the source closure. Apply Rq*.
Transpose the exact open adjunctions
to identify j! u! with (ju)!, and use the canonical derived direct-image compositor
to identify Rr* Rq* with R(rq)*. This gives the displayed isomorphism. Only one
triple is claimed, so no comparison between auxiliary choices is required. -/
theorem exists_localizingLowerShriekComposition_model
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (_hΛ : Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    [QuasiCompact (Z ↘ Spec (.of k))]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g] :
    ∃ (cf : Compactification.BoundaryCompactification f)
      (cg : Compactification.BoundaryCompactification g)
      (cgf : Compactification.BoundaryCompactification (f ≫ g)),
      Nonempty (((localizingClosureProEtale Λ X).ι ⋙
          rightDerivedLowerShriekOfCompactification Λ cf.obj.obj ⋙
          rightDerivedLowerShriekOfCompactification Λ cg.obj.obj) ≅
        compactificationLocalizingCandidate Λ cgf) := by
  classical
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (Z ↘ Spec (.of k))
  have : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated (Z ↘ Spec (.of k))
  let cf : Compactification f := denseCompactification f
  let cg : Compactification g := denseCompactification g
  have : QuasiCompact cf.i := cf.quasiCompact_openImmersion inferInstance
  have : QuasiCompact cg.i := cg.quasiCompact_openImmersion inferInstance
  let : cf.Z.Over (Spec (.of k)) := ⟨cf.g ≫ (Y ↘ Spec (.of k))⟩
  let : cg.Z.Over (Spec (.of k)) := ⟨cg.g ≫ (Z ↘ Spec (.of k))⟩
  have : cf.g.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : cg.g.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : cf.i.IsOver (Spec (.of k)) := ⟨by
    change cf.i ≫ cf.g ≫ (Y ↘ Spec (.of k)) = _
    rw [← Category.assoc, ← cf.comm, comp_over]⟩
  have : cg.i.IsOver (Spec (.of k)) := ⟨by
    change cg.i ≫ cg.g ≫ (Z ↘ Spec (.of k)) = _
    rw [← Category.assoc, ← cg.comm, comp_over]⟩
  have : LocallyOfFiniteType (cg.Z ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (cg.g ≫ (Z ↘ Spec (.of k)))
    infer_instance
  have : QuasiCompact (cg.Z ↘ Spec (.of k)) := by
    change QuasiCompact (cg.g ≫ (Z ↘ Spec (.of k)))
    infer_instance
  have : IsSeparated (cg.Z ↘ Spec (.of k)) := by
    change IsSeparated (cg.g ≫ (Z ↘ Spec (.of k)))
    infer_instance
  have : CompactSpace cg.Z :=
    QuasiCompact.compactSpace_of_compactSpace (cg.Z ↘ Spec (.of k))
  have : QuasiSeparatedSpace cg.Z :=
    quasiSeparatedSpace_of_quasiSeparated (cg.Z ↘ Spec (.of k))
  let cr : Compactification (cf.g ≫ cg.i) := denseCompactification (cf.g ≫ cg.i)
  have : QuasiCompact cr.i := cr.quasiCompact_openImmersion inferInstance
  let cgf : Compactification (f ≫ g) :=
    { Z := cr.Z
      i := cf.i ≫ cr.i
      g := cr.g ≫ cg.g
      comm := by
        calc
          f ≫ g = (cf.i ≫ cf.g) ≫ (cg.i ≫ cg.g) :=
            congrArg₂ (fun a b ↦ a ≫ b) cf.comm cg.comm
          _ = cf.i ≫ (cf.g ≫ cg.i) ≫ cg.g := by simp only [Category.assoc]
          _ = cf.i ≫ (cr.i ≫ cr.g) ≫ cg.g :=
            congrArg (fun a ↦ cf.i ≫ a ≫ cg.g) cr.comm
          _ = (cf.i ≫ cr.i) ≫ cr.g ≫ cg.g := by simp only [Category.assoc]
      isOpenImmersion := inferInstance
      isProper := inferInstance }
  let bf : Compactification.BoundaryCompactification f := ⟨⟨cf, inferInstance⟩⟩
  let bg : Compactification.BoundaryCompactification g := ⟨⟨cg, inferInstance⟩⟩
  let bgf : Compactification.BoundaryCompactification (f ≫ g) :=
    ⟨⟨cgf, inferInstance⟩⟩
  have : LocallyOfFiniteType (cf.Z ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (cf.g ≫ (Y ↘ Spec (.of k)))
    infer_instance
  have : QuasiCompact (cf.Z ↘ Spec (.of k)) := by
    change QuasiCompact (cf.g ≫ (Y ↘ Spec (.of k)))
    infer_instance
  have : IsSeparated (cf.Z ↘ Spec (.of k)) := by
    change IsSeparated (cf.g ≫ (Y ↘ Spec (.of k)))
    infer_instance
  let : cr.Z.Over (Spec (.of k)) := ⟨cr.g ≫ (cg.Z ↘ Spec (.of k))⟩
  have : cr.g.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : cr.i.IsOver (Spec (.of k)) := ⟨by
    change cr.i ≫ cr.g ≫ (cg.Z ↘ Spec (.of k)) = _
    rw [← Category.assoc, ← cr.comm, comp_over]⟩
  have : LocallyOfFiniteType (cr.Z ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (cr.g ≫ (cg.Z ↘ Spec (.of k)))
    infer_instance
  have : QuasiCompact (cr.Z ↘ Spec (.of k)) := by
    change QuasiCompact (cr.g ≫ (cg.Z ↘ Spec (.of k)))
    infer_instance
  have : IsSeparated (cr.Z ↘ Spec (.of k)) := by
    change IsSeparated (cr.g ≫ (cg.Z ↘ Spec (.of k)))
    infer_instance
  have : IsSchemeTheoreticallyDominant cr.i := denseCompactification_isDense _
  let br : Compactification.BoundaryCompactification (cf.g ≫ cg.i) :=
    ⟨⟨cr, inferInstance⟩⟩
  have hcoef := _hΛ
  have hi := (properOpenInterchange Λ cf.g cg.i br ℓ k (by
    rcases hcoef with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, Or.inr h⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h))))).2
  obtain ⟨τ, hτ⟩ := exists_interchangeNatTrans Λ cf.g cg.i br (by
    intro A
    obtain ⟨m, hm, hu, _⟩ := hi A
    exact ⟨m, hm, hu⟩)
  have eo : (openImmersionLowerShriek Λ cf.i).mapDerivedCategory ⋙
      (openImmersionLowerShriek Λ cr.i).mapDerivedCategory ≅
      (openImmersionLowerShriek Λ (cf.i ≫ cr.i)).mapDerivedCategory := by
    apply Adjunction.leftAdjointUniq
      ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ cf.i).comp
        (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ cr.i))
    exact (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ (cf.i ≫ cr.i)).ofNatIsoRight
      (Functor.mapDerivedCategoryNatIso (upperStarComp Λ cf.i cr.i) ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm)
  have er := (directImageComposition Λ cr.g cg.g).symm
  have hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ := by
    rcases _hΛ with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨E, h⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
  obtain ⟨_, _, hJ, _, _⟩ :=
    (openImmersionLowerShriek_localizing ℓ k (ringChar k) ((Fact.out : (ringChar k).Prime).pos)
      (Fact.out : ringChar k ≠ ℓ) Λ hΛ cf.i).2.2
  have hτiso : ∀ K : (localizingClosureProEtale Λ X).FullSubcategory,
      IsIso (τ.app ((openImmersionLowerShriek Λ cf.i).mapDerivedCategory.obj K.obj)) := by
    intro K
    obtain ⟨m, _, hu, hIso⟩ :=
      hi ((openImmersionLowerShriek Λ cf.i).mapDerivedCategory.obj K.obj)
    rw [hu _ (hτ _)]
    exact hIso (hJ K)
  let eI : ((localizingClosureProEtale Λ X).ι ⋙
      (openImmersionLowerShriek Λ cf.i).mapDerivedCategory ⋙
      (lowerStar Λ cf.g).rightDerivedFunctor ⋙
      (openImmersionLowerShriek Λ cg.i).mapDerivedCategory) ≅
      ((localizingClosureProEtale Λ X).ι ⋙
      (openImmersionLowerShriek Λ cf.i).mapDerivedCategory ⋙
      (openImmersionLowerShriek Λ cr.i).mapDerivedCategory ⋙
      (lowerStar Λ cr.g).rightDerivedFunctor) := NatIso.ofComponents
    (fun K : (localizingClosureProEtale Λ X).FullSubcategory ↦
      @asIso _ _ _ _ (τ.app
        ((openImmersionLowerShriek Λ cf.i).mapDerivedCategory.obj K.obj)) (hτiso K))
    (fun v ↦ τ.naturality ((openImmersionLowerShriek Λ cf.i).mapDerivedCategory.map v.hom))
  refine ⟨bf, bg, bgf, ⟨?_⟩⟩
  exact Functor.isoWhiskerRight eI (lowerStar Λ cg.g).rightDerivedFunctor ≪≫
    Functor.isoWhiskerLeft ((localizingClosureProEtale Λ X).ι ⋙
      (openImmersionLowerShriek Λ cf.i).mapDerivedCategory ⋙
      (openImmersionLowerShriek Λ cr.i).mapDerivedCategory) er ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (localizingClosureProEtale Λ X).ι eo)
      (lowerStar Λ (cr.g ≫ cg.g)).rightDerivedFunctor

end AlgebraicGeometry.ProEtale.CondensedRing
