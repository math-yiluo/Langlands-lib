/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralLocalizingCompactSupport
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Noetherian

/-! # Finite-open descent for integral restriction

Source: blueprint main-20261015, sk-thm-int-restriction-glue.proof.md,
expanded by theorem-f-shriek-ell-adic-coefficients.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.IntegralRestriction

private theorem scalarModelPullbackIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ) :
    Nonempty ((CondensedRing.upperStar Λ f).obj
      (((upperStarFromPoint Y).mapMod Λ).obj P) ≅
      ((upperStarFromPoint X).mapMod Λ).obj P) := by
  refine ⟨?_⟩
  let α := condensedPullbackHom Λ f
  let e := Functor.mapModCompIso (upperStarFromPoint Y) (ProEtale.upperStar Ab.{u + 1} f)
    (upperStarFromPointComp f).hom Λ
  change (Mod.extendScalars α).obj
    (((ProEtale.upperStar Ab.{u + 1} f).mapMod _).obj
      (((upperStarFromPoint Y).mapMod Λ).obj P)) ≅ _
  refine (Mod.extendScalars α).mapIso (e.app P) ≪≫ ?_
  refine (Mod.extendScalarsIsoComapInv α).app _ ≪≫ ?_
  exact ((Mod.comapComp (asIso α).inv α).symm ≪≫
    Mod.comapCongr (by simp) ≪≫ Mod.comapId _).app
      (((upperStarFromPoint X).mapMod Λ).obj P)

private theorem finiteModel_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : HasFiniteConstantLocalModel Λ X M) :
    HasFiniteConstantLocalModel Λ X N := by
  obtain ⟨U, hU⟩ := hM
  refine ⟨U, fun i ↦ ?_⟩
  obtain ⟨P, hP, ⟨eP⟩⟩ := hU i
  exact ⟨P, hP, ⟨((CondensedRing.upperStar Λ (U.f i)).mapIso e).symm ≪≫ eP⟩⟩

private theorem square_pullback_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y V W : Scheme.{u}}
    (f : X ⟶ Y) (g : V ⟶ Y) (a : W ⟶ X) (b : W ⟶ V)
    (h : a ≫ f = b ≫ g)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) :
    Nonempty ((CondensedRing.upperStar Λ a).obj ((CondensedRing.upperStar Λ f).obj M) ≅
      (CondensedRing.upperStar Λ b).obj ((CondensedRing.upperStar Λ g).obj M)) := by
  exact ⟨((CondensedRing.upperStarComp Λ a f).app M).symm ≪≫
    eqToIso (congrArg (fun q ↦ (CondensedRing.upperStar Λ q).obj M) h) ≪≫
    (CondensedRing.upperStarComp Λ b g).app M⟩

private theorem finiteModel_square
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y V W : Scheme.{u}}
    (f : X ⟶ Y) (g : V ⟶ Y) (a : W ⟶ X) (b : W ⟶ V)
    (h : a ≫ f = b ≫ g)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hM : ∃ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ,
      Mod.IsFinitelyPresented Λ P ∧ Nonempty ((CondensedRing.upperStar Λ g).obj M ≅
        ((upperStarFromPoint V).mapMod Λ).obj P)) :
    ∃ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ,
      Mod.IsFinitelyPresented Λ P ∧
        Nonempty ((CondensedRing.upperStar Λ a).obj ((CondensedRing.upperStar Λ f).obj M) ≅
          ((upperStarFromPoint W).mapMod Λ).obj P) := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := hM
  obtain ⟨e⟩ := scalarModelPullbackIso Λ b P
  obtain ⟨ec⟩ := square_pullback_iso Λ f g a b h M
  exact ⟨P, hP, ⟨ec ≪≫ (CondensedRing.upperStar Λ b).mapIso eP ≪≫ e⟩⟩

private theorem finiteModel_cover
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (U : Scheme.Cover.{u} Scheme.proetalePrecoverage Y)
    (V : Scheme.Cover.{u} Scheme.proetalePrecoverage X)
    (a : V.I₀ → U.I₀) (b : ∀ i, V.X i ⟶ U.X (a i))
    (hb : ∀ i, V.f i ≫ f = b i ≫ U.f (a i))
    (hU : ∀ i, ∃ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ,
      Mod.IsFinitelyPresented Λ P ∧ Nonempty ((CondensedRing.upperStar Λ (U.f i)).obj M ≅
        ((upperStarFromPoint (U.X i)).mapMod Λ).obj P)) :
    HasFiniteConstantLocalModel Λ X ((CondensedRing.upperStar Λ f).obj M) := by
  exact ⟨V, fun i ↦ finiteModel_square Λ f (U.f (a i)) (V.f i) (b i) (hb i) M (hU (a i))⟩

private theorem finiteModel_pullback
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y))
    (hM : HasFiniteConstantLocalModel Λ Y M) :
    HasFiniteConstantLocalModel Λ X ((CondensedRing.upperStar Λ f).obj M) := by
  obtain ⟨U, hU⟩ := hM
  exact finiteModel_cover Λ f M U (U.pullback₁ f) (fun i ↦ i)
    (fun i ↦ pullback.snd f (U.f i)) (fun _ ↦ pullback.condition) hU

private theorem finiteModel_composite
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
    (hM : HasFiniteConstantLocalModel Λ X
      ((CondensedRing.upperStar Λ f).obj ((CondensedRing.upperStar Λ g).obj M))) :
    HasFiniteConstantLocalModel Λ X ((CondensedRing.upperStar Λ (f ≫ g)).obj M) := by
  exact finiteModel_of_iso Λ ((CondensedRing.upperStarComp Λ f g).app M).symm hM

private theorem finiteModel_factoring
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {W : Scheme.{u}} (q : W ⟶ X) (j : W ⟶ Z) (hq : q ≫ (f ≫ g) = j)
    (M : Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z))
    (hM : HasFiniteConstantLocalModel Λ X
      ((CondensedRing.upperStar Λ f).obj ((CondensedRing.upperStar Λ g).obj M))) :
    HasFiniteConstantLocalModel Λ W ((CondensedRing.upperStar Λ j).obj M) := by
  subst j
  exact finiteModel_composite Λ q (f ≫ g) M
    (finiteModel_pullback Λ q _ (finiteModel_composite Λ f g M hM))

-- The disjoint-first-open refinement of the source-library gluing core,
-- using Noetherian compactness in place of affineness of the covering opens.
private theorem noetherian_stratification_factoring_local
    {X : Scheme.{u}} [IsNoetherian X]
    (n : ℕ) (W : Fin n → X.Opens)
    (hcover : (⋃ a : Fin n, (W a : Set X)) = Set.univ)
    (T : ∀ a, Stratification (W a))
    (hc : ∀ a b, Topology.IsConstructible ((T a).stratum b)) :
    ∃ S : Stratification X,
      (∀ i, Topology.IsConstructible (S.stratum i)) ∧
      ∀ i, ∃ (a : Fin n) (b : Fin (T a).n)
        (q : S.domain i ⟶ (T a).domain b),
        q ≫ ((T a).immersion b ≫ (W a).ι) = S.immersion i := by
  classical
  let V (a : Fin n) : Set X := ⋃ b ∈ {b : Fin n | b < a}, (W b : Set X)
  have hVo (a : Fin n) : IsOpen (V a) :=
    isOpen_iUnion fun b ↦ isOpen_iUnion fun _ ↦ (W b).isOpen
  have hVc (a : Fin n) : Topology.IsConstructible (V a) :=
    .biUnion (Set.toFinite _) fun b _ ↦
      (TopologicalSpace.NoetherianSpace.isCompact _).isConstructible (W b).isOpen
  let I (a : Fin n) := IdealSheafData.vanishingIdeal (⟨(V a)ᶜ, (hVo a).isClosed_compl⟩)
  let c (a : Fin n) := (I a).subschemeι
  have hcr (a : Fin n) : Set.range (c a) = (V a)ᶜ := by
    simp [c, I, IdealSheafData.range_subschemeι]
  let K := (a : Fin n) × Fin (T a).n
  let e : Fin (Fintype.card K) ≃ K := (Fintype.equivFin K).symm
  let g (k : K) := (T k.1).immersion k.2 ≫ (W k.1).ι
  have hg (k : K) : IsImmersion (g k) := by
    have := (T k.1).isImmersion k.2
    dsimp [g]
    infer_instance
  let f (k : K) := pullback.fst (g k) (c k.1) ≫ g k
  have hf (k : K) : IsImmersion (f k) := by
    have := hg k
    dsimp [f, c]
    infer_instance
  have hgr (k : K) : Set.range (g k) = (W k.1).ι '' (T k.1).stratum k.2 := by
    rw [Hom.comp_base, TopCat.coe_comp, Set.range_comp, (T k.1).range_immersion]
  have hfr (k : K) : Set.range (f k) = Set.range (g k) ∩ (V k.1)ᶜ := by
    rw [Hom.comp_base, TopCat.coe_comp, Set.range_comp, Pullback.range_fst, hcr,
      Set.image_preimage_eq_inter_range, Set.inter_comm]
  have hgc (k : K) : Topology.IsConstructible (Set.range (g k)) := by
    rw [hgr]
    apply (hc k.1 k.2).image_of_isOpenEmbedding (W k.1).ι.isOpenEmbedding
    rw [Opens.range_ι]
    exact (TopologicalSpace.NoetherianSpace.isCompact _).isRetrocompact (W k.1).isOpen
  have hfc (k : K) : Topology.IsConstructible (Set.range (f k)) := by
    rw [hfr]
    exact (hgc k).inter (hVc k.1).compl
  have hdis : Pairwise (fun k l : K ↦ Disjoint (Set.range (f k)) (Set.range (f l))) := by
    intro k l hkl
    apply Set.disjoint_left.mpr
    intro x hx hy
    rw [hfr] at hx hy
    rw [hgr] at hx hy
    by_cases ha : k.1 = l.1
    · rcases k with ⟨a, b⟩
      rcases l with ⟨a', b'⟩
      dsimp at ha
      subst a'
      have hb : b ≠ b' := fun h ↦ hkl (by cases h; rfl)
      obtain ⟨z, hz, hzx⟩ := hx.1
      obtain ⟨w, hw, hwx⟩ := hy.1
      have hzw : z = w := (W a).ι.isOpenEmbedding.injective (hzx.trans hwx.symm)
      exact Set.disjoint_left.mp ((T a).pairwise_disjoint_stratum hb) hz (hzw ▸ hw)
    · rcases lt_or_gt_of_ne ha with hal | hla
      · apply hy.2
        exact Set.mem_iUnion.mpr ⟨k.1, Set.mem_iUnion.mpr ⟨hal, by
          obtain ⟨z, _, rfl⟩ := hx.1
          exact z.property⟩⟩
      · apply hx.2
        exact Set.mem_iUnion.mpr ⟨l.1, Set.mem_iUnion.mpr ⟨hla, by
          obtain ⟨z, _, rfl⟩ := hy.1
          exact z.property⟩⟩
  have hcoverf : (⋃ k : K, Set.range (f k)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hex : ∃ a : Fin n, x ∈ (W a : Set X) :=
      Set.mem_iUnion.mp (hcover.symm ▸ Set.mem_univ x)
    obtain ⟨a, hax, hmin⟩ := Set.exists_min_image {a : Fin n | x ∈ (W a : Set X)}
      (fun a ↦ a) (Set.toFinite _) hex
    let y : W a := ⟨x, hax⟩
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp
      ((T a).iUnion_stratum_eq_univ.symm ▸ Set.mem_univ y)
    refine Set.mem_iUnion.mpr ⟨⟨a, b⟩, ?_⟩
    rw [hfr, hgr]
    refine ⟨⟨y, hb, rfl⟩, ?_⟩
    intro hxV
    obtain ⟨a', hxV⟩ := Set.mem_iUnion.mp hxV
    obtain ⟨ha', hxa'⟩ := Set.mem_iUnion.mp hxV
    exact (not_lt_of_ge (hmin a' hxa')) ha'
  let S : Stratification X := {
    n := Fintype.card K
    stratum := fun i ↦ Set.range (f (e i))
    isLocallyClosed_stratum := fun i ↦ (f (e i)).isLocallyClosed_range
    isConstructible_stratum := fun i ↦ hfc (e i)
    iUnion_stratum_eq_univ := by
      rw [← hcoverf]
      exact e.surjective.iUnion_comp (fun k ↦ Set.range (f k))
    pairwise_disjoint_stratum := fun i j hij ↦ hdis (e.injective.ne hij)
    domain := fun i ↦ pullback (g (e i)) (c (e i).1)
    immersion := fun i ↦ f (e i)
    isImmersion := fun i ↦ hf (e i)
    range_immersion := fun i ↦ rfl }
  refine ⟨S, S.isConstructible_stratum, ?_⟩
  intro i
  exact ⟨(e i).1, (e i).2, pullback.fst _ _, rfl⟩

private theorem finiteStrat_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X : Scheme.{u}}
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsFiniteConstantStratified Λ X M) :
    IsFiniteConstantStratified Λ X N := by
  obtain ⟨S, hS⟩ := hM
  exact ⟨S, fun a ↦ finiteModel_of_iso Λ
    ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e) (hS a)⟩

private def stratifiedOnOpen
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (H : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (U : X.Opens) : Prop :=
  IsFiniteConstantStratified Λ U.toScheme ((CondensedRing.upperStar Λ U.ι).obj H)

private theorem cohomology_local_stratified
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) [IsNoetherian X]
    (U : X.Opens) (M : Ambient Λ X) (n : ℤ)
    (hM : generators Λ U.toScheme ((pull Λ U.ι).obj M)) :
    stratifiedOnOpen Λ X ((DerivedCategory.homologyFunctor _ n).obj M) U := by
  have : CompactSpace U.toScheme :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (U : Set X))
  have hi := hM.2 n
  have he := (leftDerivedUpperStarIsoMapDerivedCategory Λ U.ι).app M
  have eh := ((CondensedRing.upperStar Λ U.ι).mapDerivedCategoryHomologyFunctorIso n).app M
  have hqc : CompactSpace U.toScheme ∧ QuasiSeparatedSpace U.toScheme :=
    ⟨inferInstance, inferInstance⟩
  have hi' : IsFiniteConstantStratified Λ U.toScheme
      ((DerivedCategory.homologyFunctor _ n).obj ((pull Λ U.ι).obj M)) := by
    simpa only [IsConstantModelConstructible, ite_eq_left hqc] using hi
  exact finiteStrat_of_iso Λ
    (((DerivedCategory.homologyFunctor _ n).mapIso he) ≪≫ eh.symm) hi'

private theorem finiteStrat_of_factoring
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u})
    (n : ℕ) (W : Fin n → X.Opens)
    (H : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (T : ∀ a, Stratification (W a))
    (hT : ∀ a b, HasFiniteConstantLocalModel Λ ((T a).domain b)
      ((CondensedRing.upperStar Λ ((T a).immersion b)).obj
        ((CondensedRing.upperStar Λ (W a).ι).obj H)))
    (S : Stratification X)
    (hS : ∀ j, ∃ (a : Fin n) (b : Fin (T a).n)
      (q : S.domain j ⟶ (T a).domain b),
      q ≫ ((T a).immersion b ≫ (W a).ι) = S.immersion j) :
    IsFiniteConstantStratified Λ X H := by
  refine ⟨S, fun j ↦ ?_⟩
  obtain ⟨a, b, q, hq⟩ := hS j
  exact finiteModel_factoring Λ ((T a).immersion b) (W a).ι q
    (S.immersion j) hq H (hT a b)

private theorem finiteStrat_open_descent_explicit
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) [IsNoetherian X]
    (n : ℕ) (W : Fin n → X.Opens) (hc : (⋃ a, (W a : Set X)) = Set.univ)
    (H : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (T : ∀ a, Stratification (W a))
    (hT : ∀ a b, HasFiniteConstantLocalModel Λ ((T a).domain b)
      ((CondensedRing.upperStar Λ ((T a).immersion b)).obj
        ((CondensedRing.upperStar Λ (W a).ι).obj H))) :
    IsFiniteConstantStratified Λ X H := by
  obtain ⟨S, _, hS⟩ := noetherian_stratification_factoring_local n W hc T
    (fun a b ↦ (T a).isConstructible_stratum b)
  exact finiteStrat_of_factoring Λ X n W H T hT S hS

private theorem choose_apply {A : Type*} {B : A → Type*}
    {P : (a : A) → B a → Prop} {Q : Prop}
    (h : ∀ a, ∃ b, P a b) (k : ∀ b : (a : A) → B a, (∀ a, P a (b a)) → Q) : Q := by
  classical
  choose b hb using h
  exact k b hb

private theorem finiteStrat_open_descent
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) [IsNoetherian X]
    (n : ℕ) (W : Fin n → X.Opens) (hc : (⋃ a, (W a : Set X)) = Set.univ)
    (H : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hlocal : ∀ a, stratifiedOnOpen Λ X H (W a)) : IsFiniteConstantStratified Λ X H := by
  classical
  exact choose_apply hlocal (fun T hT ↦
    finiteStrat_open_descent_explicit Λ X n W hc H T hT)

private theorem finiteCover_reindex
    (X : Scheme.{u}) (P : X.Opens → Prop) (Q : Prop)
    (h : ∀ (n : ℕ) (W : Fin n → X.Opens),
      (⋃ a, (W a : Set X)) = Set.univ → (∀ a, P (W a)) → Q)
    (I : Type w) [Finite I] (U : I → X.Opens) (hc : iSup U = ⊤)
    (hlocal : ∀ a, P (U a)) : Q := by
  classical
  let := Fintype.ofFinite I
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  apply h _ (fun a ↦ U (e a)) ?_ (fun a ↦ hlocal (e a))
  apply Set.eq_univ_of_forall
  intro x
  have hx : x ∈ iSup U := by rw [hc]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact Set.mem_iUnion.mpr ⟨e.symm i, by simpa using hi⟩

private theorem finiteStrat_finite_index
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) [IsNoetherian X]
    (I : Type w) [Finite I] (U : I → X.Opens) (hc : iSup U = ⊤)
    (H : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hlocal : ∀ a, stratifiedOnOpen Λ X H (U a)) : IsFiniteConstantStratified Λ X H := by
  exact finiteCover_reindex X (stratifiedOnOpen Λ X H) _
    (fun n W hc hlocal ↦ finiteStrat_open_descent Λ X n W hc H hlocal) I U hc hlocal

/-- Finite constant-model constructibility of all cohomology modules descends.
Source: theorem-f-shriek-ell-adic-coefficients, proof steps 1 and 3; blueprint
sk-thm-int-restriction-glue.proof.md, paragraph (1).
(blueprint: lem-int-restriction-cohomology-descent).

Proof: Exact restriction identifies the cohomology of each restricted complex
with the restriction of its global cohomology. Reindex the finite cover by Fin n.
For each open choose a finite constructible locally closed stratification. For an
index a let V_a be the union of the earlier opens. Intersect each stratum of U_a
with the closed complement of V_a, using its reduced closed subscheme and an actual
fibre product of immersions. These strata are constructible by Noetherianity and
locally closed by stability of immersions. They are disjoint: distinct open indices
cannot both be the first containing index, and strata within one open are disjoint.
They cover X by choosing the least containing open and then its unique stratum.
Each new stratum has an explicit projection into its original local stratum.
Pull back the original pro-etale cover and its fixed finitely presented scalar
module along that projection. The inverse-image composition comparison and the
point-pullback comparison, together with extension/comap cancellation for the
Cartesian coefficient isomorphism, identify the pulled-back model with that same
scalar module pulled back from the point. This proves finite constant stratified
constructibility in each degree. The empty cover gives an empty stratification
and forces X empty, so is covered by the same construction. -/
theorem cohomology_finiteOpenDescent
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) [IsNoetherian X] (I : Type w) [Finite I] (U : I → X.Opens)
    (hcover : iSup U = ⊤) (M : Ambient Λ X)
    (hM : ∀ i : I, generators Λ (U i).toScheme ((pull Λ (U i).ι).obj M)) :
    ∀ n : ℤ, IsConstantModelConstructible Λ X
      ((DerivedCategory.homologyFunctor _ n).obj M) := by
  intro n
  have hqc : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  simp only [IsConstantModelConstructible, ite_eq_left hqc]
  exact finiteStrat_finite_index Λ X I U hcover _
    (fun a ↦ cohomology_local_stratified Λ X (U a) M n (hM a))

end AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.IntegralRestriction
