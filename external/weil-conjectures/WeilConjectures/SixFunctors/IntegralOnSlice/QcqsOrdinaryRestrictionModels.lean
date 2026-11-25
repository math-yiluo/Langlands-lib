/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionOrdinaryModels
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsOrdinaryRestrictionExact
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsOrdinaryQuotientRestriction
import all WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingRoosComparison
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels

/-! Source: Stacks Tags 099M, 09BL and 09BM; blueprint: lem-fix-qcqs-ordinary-restriction-models.
This is a separately stated component of the locality argument. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOnSlice
section RoosRestriction
universe a b c d
open CochainComplex CochainComplex.HomComplex
variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
  {B : Type c} [Category.{d} B] [Abelian B] [HasCountableProducts B]

-- The coordinate matrix proof also works when only countable products are preserved.
private theorem restrictionRoosIsIso (F : A ⥤ B) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) : IsIso (scalarRoosMap F C) := by
  let G := F.mapHomologicalComplex (.up ℤ)
  let pc : G.obj (∏ᶜ fun n : ℕ ↦ C.obj (op n)) ⟶
      ∏ᶜ fun n : ℕ ↦ G.obj (C.obj (op n)) :=
    piComparison G (fun n : ℕ ↦ C.obj (op n))
  have hpc : IsIso pc := by dsimp only [pc]; infer_instance
  obtain ⟨hf, hs⟩ := podReindexingRoosCoordinates F C
  let : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  have hpcf (i : ℤ) : IsIso (pc.f i) := inferInstance
  have hi (i : ℤ) : IsIso ((scalarRoosMap F C).f i) := by
    let eY := coconeCoordinates (scalarRoosBoundary C) i
    let eX := coconeCoordinates (scalarRoosBoundary (C ⋙ G)) i
    have he : F.map eY.hom ≫
        (F.mapBiprod ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X i)
          ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X (i - 1))).hom =
        biprod.lift (F.map ((mappingCocone.fst (scalarRoosBoundary C)).f i))
          (F.map ((mappingCocone.snd (scalarRoosBoundary C)).v
            i (i - 1) (by omega))) :=
      biprod.map_lift_mapBiprod F _ _ _ _
    have hm : (scalarRoosMap F C).f i ≫ eX.hom =
        F.map eY.hom ≫ (F.mapBiprod ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X i)
            ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X (i - 1))).hom ≫
          biprod.map (pc.f i) (pc.f (i - 1)) := by
      rw [← Category.assoc, he]
      apply biprod.hom_ext
      · dsimp only [eX, coconeCoordinates]
        simp only [Category.assoc]
        erw [biprod.lift_fst, biprod.map_fst, biprod.lift_fst_assoc]
        exact congrArg (fun f ↦ f.f i) hf
      · dsimp only [eX, coconeCoordinates]
        simp only [Category.assoc]
        erw [biprod.lift_snd, biprod.map_snd, biprod.lift_snd_assoc]
        exact hs i
    have : IsIso ((scalarRoosMap F C).f i ≫ eX.hom) := by
      rw [hm]
      change IsIso (((F.mapIso eY) ≪≫
        F.mapBiprod ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X i)
          ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X (i - 1)) ≪≫
        biprod.mapIso (asIso (pc.f i)) (asIso (pc.f (i - 1)))).hom)
      infer_instance
    exact IsIso.of_isIso_comp_right _ eX.hom
  exact HomologicalComplex.Hom.isIso_of_components _

-- Use the prescribed cochain degree directly, without rewriting a dependent index.
private theorem restrictionRoosSnd (F : A ⥤ B) [F.Additive]
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) (i j : ℤ) (hij : i + -1 = j) :
    (scalarRoosMap F C).f i ≫ (mappingCocone.snd
        (scalarRoosBoundary (C ⋙ F.mapHomologicalComplex (.up ℤ)))).v i j hij =
      F.map ((mappingCocone.snd (scalarRoosBoundary C)).v i j hij) ≫
        (piComparison (F.mapHomologicalComplex (.up ℤ))
          (fun n : ℕ ↦ C.obj (op n))).f j := by
  let G := F.mapHomologicalComplex (.up ℤ)
  let pc := piComparison G (fun n : ℕ ↦ C.obj (op n))
  apply (isLimitOfHasProductOfPreservesLimit
    (HomologicalComplex.eval B (.up ℤ) j)
    (fun n : ℕ ↦ G.obj (C.obj (op n)))).hom_ext
  rintro ⟨n⟩
  change ((scalarRoosMap F C).f i ≫
      (mappingCocone.snd (scalarRoosBoundary (C ⋙ G))).v i j hij) ≫
        (Pi.π (fun n : ℕ ↦ G.obj (C.obj (op n))) n).f j = _
  simp only [Category.assoc]
  have h := (scalarRoosMap_existsUnique F C).exists.choose_spec.2 i j hij n
  change (scalarRoosMap F C).f i ≫
      (mappingCocone.snd (scalarRoosBoundary (C ⋙ G))).v i j hij ≫
        (Pi.π (fun n : ℕ ↦ G.obj (C.obj (op n))) n).f j = _ at h
  rw [h]
  have hp := congrArg (fun f ↦ f.f j)
    (piComparison_comp_π G (fun n : ℕ ↦ C.obj (op n)) n)
  change pc.f j ≫ (Pi.π (fun n : ℕ ↦ G.obj (C.obj (op n))) n).f j =
      F.map ((Pi.π (fun n : ℕ ↦ C.obj (op n)) n).f j) at hp
  exact (F.map_comp _ _).trans
    (congrArg (F.map ((mappingCocone.snd (scalarRoosBoundary C)).v i j hij) ≫ ·) hp.symm)

private theorem restrictionRoosModels (F : A ⥤ B) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    (T : CochainComplex A ℤ ⥤ ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (U : CochainComplex B ℤ ⥤ ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (τ : T ⋙ (Functor.whiskeringRight _ _ _).obj (F.mapHomologicalComplex (.up ℤ)) ≅
      F.mapHomologicalComplex (.up ℤ) ⋙ U) :
    ∃ χ : (T ⋙ integralOperationsRoosFunctor) ⋙ F.mapHomologicalComplex (.up ℤ) ≅
        F.mapHomologicalComplex (.up ℤ) ⋙ (U ⋙ integralOperationsRoosFunctor),
      (∀ P, χ.hom.app P ≫ mappingCocone.fst
          (scalarRoosBoundary (U.obj ((F.mapHomologicalComplex (.up ℤ)).obj P))) =
        (F.mapHomologicalComplex (.up ℤ)).map
            (mappingCocone.fst (scalarRoosBoundary (T.obj P))) ≫
          piComparison (F.mapHomologicalComplex (.up ℤ)) (fun n : ℕ ↦ (T.obj P).obj (op n)) ≫
          Limits.Pi.map (fun n : ℕ ↦ (τ.hom.app P).app (op n))) ∧
      (∀ (P : CochainComplex A ℤ) (j : ℤ),
        (χ.hom.app P).f j ≫ (mappingCocone.snd
            (scalarRoosBoundary (U.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)))).v
              j (j + -1) rfl =
          F.map ((mappingCocone.snd (scalarRoosBoundary (T.obj P))).v j (j + -1) rfl) ≫
            (piComparison (F.mapHomologicalComplex (.up ℤ))
              (fun n : ℕ ↦ (T.obj P).obj (op n))).f (j + -1) ≫
            (Limits.Pi.map (fun n : ℕ ↦ (τ.hom.app P).app (op n))).f (j + -1)) := by
  let G := F.mapHomologicalComplex (.up ℤ)
  have hχ (P : CochainComplex A ℤ) : IsIso (scalarRoosMap F (T.obj P)) :=
    restrictionRoosIsIso F _
  let χ : (T ⋙ integralOperationsRoosFunctor) ⋙ G ≅
      G ⋙ (U ⋙ integralOperationsRoosFunctor) := NatIso.ofComponents
    (fun P ↦ by
      letI := hχ P
      exact asIso (scalarRoosMap F (T.obj P)) ≪≫
        integralOperationsRoosFunctor.mapIso (τ.app P)) (by
      intro P Q a
      change G.map (integralOperationsRoosMap (T.map a)) ≫
          (scalarRoosMap F (T.obj Q) ≫ integralOperationsRoosMap (τ.hom.app Q)) =
        (scalarRoosMap F (T.obj P) ≫ integralOperationsRoosMap (τ.hom.app P)) ≫
          integralOperationsRoosMap (U.map (G.map a))
      dsimp only [G]
      rw [← Category.assoc, podReindexingRoosNaturality]
      simp only [Category.assoc]
      rw [← integralOperationsRoosMap_comp, ← integralOperationsRoosMap_comp]
      exact congrArg (scalarRoosMap F (T.obj P) ≫ ·)
        (congrArg integralOperationsRoosMap (τ.hom.naturality a)))
  refine ⟨χ, ?_, ?_⟩
  · intro P
    change (scalarRoosMap F (T.obj P) ≫ integralOperationsRoosMap (τ.hom.app P)) ≫ _ = _
    erw [Category.assoc, (IntegralAmbient.roosMap_coordinates (τ.hom.app P)).1,
      ← Category.assoc, (podReindexingRoosCoordinates F (T.obj P)).1, Category.assoc]
  · intro P j
    change (scalarRoosMap F (T.obj P) ≫ integralOperationsRoosMap (τ.hom.app P)).f j ≫ _ = _
    simp only [HomologicalComplex.comp_f, Category.assoc]
    erw [(IntegralAmbient.roosMap_coordinates (τ.hom.app P)).2 j (j + -1) rfl,
      ← Category.assoc]
    erw [restrictionRoosSnd F (T.obj P) j (j + -1) rfl, Category.assoc]

end RoosRestriction

/-- Projection-normalized strict quotient and Roos comparisons for a weakly etale
map followed by a locally closed immersion.

Source: Stacks Tags 09BL, 09BM, 06YY and 0941; Bhatt--Scholze Lemma 6.5.8.
(blueprint: lem-fix-qcqs-ordinary-restriction-models).
Proof: inverse image for an immersion preserves all limits; for a weakly etale map
it is restriction to a slice. Compose these functors. The finite constant-section
coefficient maps are isomorphisms and commute with every quotient transition.
Preservation of their inverse limit identifies the completed ring map. The resulting
module pullback is exact and preserves countable products. Tensor base change on
sections identifies each quotient reduction and its augmentation. These comparisons
commute with quotient transitions on generators, giving tau on the whole strict tower.
Apply the additive product mapping-cocone comparison and then tau to obtain chi;
both its product coordinates are the canonical product comparison followed by tau.
This is a chain-level statement: derived descent and compatibility with the
specified completion unit are proved separately. -/
theorem qcqsOrdinaryRestrictionModels
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {S V T : Scheme.{t}} [CompactSpace S] [QuasiSeparatedSpace S]
    [CompactSpace V] [QuasiSeparatedSpace V] [CompactSpace T] [QuasiSeparatedSpace T]
    (s : S ⟶ V) (i : V ⟶ T) [WeaklyEtale s] [IsImmersion i] :
    let r := s ≫ i
    PreservesFiniteLimits (ordinaryPull l E r) ∧
    PreservesFiniteColimits (ordinaryPull l E r) ∧
    IsIso (ordinaryCoefficientMap l E r) ∧
    (∃ (τ : tower l E T none ⋙
          (Functor.whiskeringRight ℕᵒᵖ (Cx l E T none) (Cx l E S none)).obj
            (ordinaryComplexPull l E r) ≅
          ordinaryComplexPull l E r ⋙ tower l E S none)
        (χ : roos l E T none ⋙ ordinaryComplexPull l E r ≅
          ordinaryComplexPull l E r ⋙ roos l E S none),
        (∀ (P : Cx l E T none) (n : ℕ),
          (ordinaryComplexPull l E r).map (((augmentation l E T none).app P).app (op n)) ≫
              (τ.hom.app P).app (op n) =
            ((augmentation l E S none).app ((ordinaryComplexPull l E r).obj P)).app (op n)) ∧
        (∀ P : Cx l E T none,
          χ.hom.app P ≫ CochainComplex.mappingCocone.fst
              (ordinaryRoosEndomorphism l E ((ordinaryComplexPull l E r).obj P)) =
            (ordinaryComplexPull l E r).map
                (CochainComplex.mappingCocone.fst (ordinaryRoosEndomorphism l E P)) ≫
              piComparison (ordinaryComplexPull l E r)
                (fun n : ℕ ↦ ((tower l E T none).obj P).obj (op n)) ≫
              Limits.Pi.map (fun n : ℕ ↦ (τ.hom.app P).app (op n))) ∧
        (∀ (P : Cx l E T none) (i : ℤ),
          (χ.hom.app P).f i ≫
              (CochainComplex.mappingCocone.snd
                (ordinaryRoosEndomorphism l E ((ordinaryComplexPull l E r).obj P))).v
                  i (i + -1) rfl =
            (ordinaryPull l E r).map
                ((CochainComplex.mappingCocone.snd (ordinaryRoosEndomorphism l E P)).v
                  i (i + -1) rfl) ≫
              (piComparison (ordinaryComplexPull l E r)
                (fun n : ℕ ↦ ((tower l E T none).obj P).obj (op n))).f (i + -1) ≫
              (Limits.Pi.map (fun n : ℕ ↦ (τ.hom.app P).app (op n))).f (i + -1))) := by
  obtain ⟨hlim, hcoeff⟩ := qcqsOrdinaryRestrictionExact l E s i
  let := hlim
  let F := ordinaryPull l E (s ≫ i)
  have hcolim : PreservesFiniteColimits F := by
    have : PreservesColimitsOfSize.{0, 0} F :=
      (ordinaryAdjunction l E (s ≫ i)).leftAdjoint_preservesColimits
    infer_instance
  obtain ⟨τ, hτ⟩ := qcqsOrdinaryQuotientRestriction l E s i
  obtain ⟨χ, hf, hs⟩ := restrictionRoosModels F
    (tower l E T none) (tower l E S none) τ
  exact ⟨inferInstance, hcolim, hcoeff, τ, χ, hτ, hf, hs⟩

end WeilConjectures.IntegralOnSlice
