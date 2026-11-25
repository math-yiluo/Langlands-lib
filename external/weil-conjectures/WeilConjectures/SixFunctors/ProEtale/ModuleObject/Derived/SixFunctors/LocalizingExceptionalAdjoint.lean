/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import all WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.CategoryTheory.BrownRepresentabilityHomLocallySmall
import WeilConjectures.CategoryTheory.Brown.BrownHypotheses
import WeilConjectures.CategoryTheory.CompactTestsRightAdjointCoproducts
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import Mathlib.CategoryTheory.Limits.FullSubcategory
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureExistence
import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# Exceptional inverse image on the localizing constructible closure

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-existence,
statement and proof; Stacks Tags 0A8F, 0A8G, 0A8D (blueprint:
theorem-existence-exceptional-inverse-image).

The lower shriek is the actual restriction of the recorded compactification composite.
The closure uses constant-model constructibility and the ordinary unbounded derived category.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Compactness transports by precomposition with an isomorphism. -/
private theorem compact_of_iso
    {C : Type*} [Category C] [Preadditive C] [HasCoproducts.{u} C]
    {K L : C} (e : K ≅ L) (hL : IsCompactObject L) : IsCompactObject K := by
  classical
  intro I A
  let d := DirectSum.map (fun i ↦ Preadditive.leftComp (A i) e.hom)
  have hd : Function.Bijective d :=
    ⟨(DirectSum.map_injective _).2 (fun i ↦ e.symm.homFromEquiv.injective),
      (DirectSum.map_surjective _).2 (fun i ↦ e.symm.homFromEquiv.surjective)⟩
  let post := Preadditive.leftComp (∐ A) e.hom
  have hp : Function.Bijective post := e.symm.homFromEquiv.bijective
  let a := DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp K (Sigma.ι A i))
  let b := DirectSum.toAddMonoid (fun i ↦ Preadditive.rightComp L (Sigma.ι A i))
  have square : a.comp d = post.comp b := by
    apply DirectSum.addHom_ext
    intro i f
    simp only [AddMonoidHom.comp_apply]
    dsimp [a, b, d]
    rw [DirectSum.map_of, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
    exact Category.assoc _ _ _
  have hb : Function.Bijective b := hL I A
  have hcomp : Function.Bijective (a ∘ d) := by
    change Function.Bijective (a.comp d)
    rw [square]
    exact hp.comp hb
  exact (Function.Bijective.of_comp_iff a hd).mp hcomp

/-- A weak generating family detects isomorphisms on all its shifts, by the cone test. -/
private theorem generators_detect_iso
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ]
    [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
    [Pretriangulated C] [CategoryTheory.IsTriangulated C]
    {I : Type u} (E : I → C) [HasCoproduct E]
    (hgen : IsTriangulatedGeneratingFamily E)
    {A B : C} (f : A ⟶ B)
    (hbij : ∀ i (n : ℤ), Function.Bijective (fun a : (E i) ⟦n⟧ ⟶ A ↦ a ≫ f)) :
    IsIso f := by
  have hbijshift (i : I) (m n : ℤ) :
      Function.Bijective (fun a : (E i) ⟦m⟧ ⟶ A⟦n⟧ ↦ a ≫ f⟦n⟧') := by
    let K := (E i) ⟦m⟧
    let adj := (shiftEquiv' C (-n) n (neg_add_cancel n)).toAdjunction
    let e : (E i) ⟦m + -n⟧ ≅ K⟦-n⟧ := (shiftFunctorAdd C m (-n)).app (E i)
    have hinj (a b : K⟦-n⟧ ⟶ A) (hab : a ≫ f = b ≫ f) : a = b := by
      apply (cancel_epi e.hom).mp
      apply (hbij i (m + -n)).1
      simpa only [Category.assoc] using congrArg (fun k ↦ e.hom ≫ k) hab
    constructor
    · intro a b hab
      apply (adj.homEquiv K A).symm.injective
      apply hinj
      have hh := congrArg (adj.homEquiv K B).symm hab
      change (adj.homEquiv K B).symm
        (a ≫ (shiftEquiv' C (-n) n (neg_add_cancel n)).inverse.map f) =
        (adj.homEquiv K B).symm
          (b ≫ (shiftEquiv' C (-n) n (neg_add_cancel n)).inverse.map f) at hh
      rw [adj.homEquiv_naturality_right_symm,
        adj.homEquiv_naturality_right_symm] at hh
      exact hh
    · intro g
      obtain ⟨a, ha⟩ := (hbij i (m + -n)).2
        (e.hom ≫ (adj.homEquiv K B).symm g)
      refine ⟨adj.homEquiv K A (e.inv ≫ a), ?_⟩
      change adj.homEquiv K A (e.inv ≫ a) ≫
        (shiftEquiv' C (-n) n (neg_add_cancel n)).inverse.map f = g
      rw [← adj.homEquiv_naturality_right]
      apply (adj.homEquiv K B).symm.injective
      simp only [Equiv.symm_apply_apply]
      change a ≫ f = e.hom ≫ (adj.homEquiv K B).symm g at ha
      rw [Category.assoc, ha]
      simp
  obtain ⟨D, d, δ, hd⟩ := Pretriangulated.distinguished_cocone_triangle f
  have hD (i : I) (m : ℤ) (a : (E i) ⟦m⟧ ⟶ D) : a = 0 := by
    have hδ : a ≫ δ = 0 := by
      apply (hbijshift i m 1).1
      have hzero := Pretriangulated.comp_distTriang_mor_zero₃₁ _ hd
      change δ ≫ f⟦(1 : ℤ)⟧' = 0 at hzero
      simp only [Category.assoc, hzero, comp_zero, zero_comp]
    obtain ⟨b, hb⟩ := Pretriangulated.Triangle.coyoneda_exact₃ _ hd a hδ
    obtain ⟨b', hb'⟩ := (hbij i m).2 b
    have hfd : f ≫ d = 0 := Pretriangulated.comp_distTriang_mor_zero₁₂ _ hd
    change a = b ≫ d at hb
    rw [hb, ← hb', Category.assoc, hfd, comp_zero]
  have hzD : IsZero D := by
    by_contra hn
    obtain ⟨n, a, ha⟩ := hgen D hn
    apply ha
    apply Sigma.hom_ext
    intro i
    let adj := (shiftEquiv' C (-n) n (neg_add_cancel n)).toAdjunction
    have : (shiftEquiv' C (-n) n (neg_add_cancel n)).functor.Additive :=
      inferInstanceAs (shiftFunctor C (-n)).Additive
    have : (shiftEquiv' C (-n) n (neg_add_cancel n)).inverse.Additive :=
      inferInstanceAs (shiftFunctor C n).Additive
    apply (adj.homEquiv (E i) D).symm.injective
    rw [hD i (-n) ((adj.homEquiv (E i) D).symm (Sigma.ι E i ≫ a))]
    simpa only [comp_zero] using (adj.homAddEquiv_symm_zero (E i) D).symm
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hd).mp hzD

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- Restrict the existing `Rp_* D(j_!)` to the recorded localizing closures, once its
preservation of these object properties is established. The proof argument supplies only
membership; objects and maps are exactly those of the ambient compactification functor.
Source: blueprint theorem-existence-exceptional-inverse-image, definition of `Rf_!`
(blueprint: theorem-existence-exceptional-inverse-image). -/
noncomputable def localizingLowerShriek (c : Compactification f)
    (h : ∀ K, localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
      ((rightDerivedLowerShriekOfCompactification Λ c).obj K)) :
    (localizingClosureProEtale Λ X).FullSubcategory ⥤
      (localizingClosureProEtale Λ Y).FullSubcategory :=
  (localizingClosureProEtale Λ Y).lift
    ((localizingClosureProEtale Λ X).ι ⋙ rightDerivedLowerShriekOfCompactification Λ c)
    (fun K ↦ h K.obj K.property)

/-- The restricted compactification functor has the shift comparison induced from its
ambient derived functor, via the fully faithful inclusions of the localizing closures.
Source: blueprint theorem-existence-exceptional-inverse-image, exactness of the restricted lower
shriek (blueprint: theorem-existence-exceptional-inverse-image). -/
noncomputable instance localizingLowerShriekCommShift (c : Compactification f)
    (h : ∀ K, localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
      ((rightDerivedLowerShriekOfCompactification Λ c).obj K))
    [(localizingClosureProEtale Λ X).IsTriangulated]
    [(localizingClosureProEtale Λ Y).IsTriangulated] :
    (localizingLowerShriek Λ c h).CommShift ℤ :=
  inferInstanceAs (((localizingClosureProEtale Λ Y).lift
    ((localizingClosureProEtale Λ X).ι ⋙ rightDerivedLowerShriekOfCompactification Λ c)
    (fun K ↦ h K.obj K.property)).CommShift ℤ)

set_option linter.unusedVariables false in
/-- The compactification lower shriek on localizing closures has an exact right adjoint,
unique up to the unique counit-compatible isomorphism, and that adjoint preserves all small
coproducts. The existential triangulated structures are proofs that the recorded object
properties are triangulated; the full subcategories inherit their ambient triangles.
Source: blueprint main-20261015, theorem-existence-exceptional-inverse-image, entire statement
(blueprint: theorem-existence-exceptional-inverse-image). The base field has finite ℓ-cohomological
dimension `hcd` (definition-cohomological-dimension), the standing hypothesis of the compactness
input of lemma-hypotheses-brown-representability (statement corrected 2026-10-29,
coord/changes/M-hcd-propagation.md).

Proof:
1. By lemma-hypotheses-brown-representability the two closures are triangulated with small
coproducts,
   and small skeletons of Dctf are compact generating sets. Finite type and separatedness
   imply qcqs. Nagata (theorem-nagata-s-compactification-theorem--1) supplies a compactification.
   For the fixed one, proposition-construction-independence-rf-shriek proves preservation of the
   closures, exactness, preservation of coproducts and preservation of Dctf by Rp_* D(j_!).
2. Apply theorem-existence-exceptional-inverse-image to this restricted functor F.
   This gives G and an adjunction whose Hom equivalences are natural in both objects.
3. Transpose the shifted counit to obtain G(N)[n] ≅ G(N[n]); Yoneda
   (theorem-existence-exceptional-inverse-image) and naturality give coherence and compatibility
   of the unit and counit with shifts. Apply theorem-existence-exceptional-inverse-image.
4. For another adjunction F ⊣ J, proposition-sp-unique-adjoint--1 transposes the two
   counits to mutually inverse natural transformations G ≅ J. Injectivity of the Hom
   equivalence gives uniqueness of the counit-compatible isomorphism.
5. For a small family N_i test the canonical comparison coproduct G(N_i) → G(coproduct N_i)
   against every shifted compact generator P[n]. Both P[n] and F(P[n]) are compact,
   by lemma-hypotheses-brown-representability and proposition-construction-independence-rf-shriek.
   Compactness (theorem-existence-exceptional-inverse-image), adjunction and naturality identify
   this test with the identity on the direct sum of Hom(F(P[n]),N_i).
6. The Hom exact sequences (theorem-existence-exceptional-inverse-image) of the comparison's
   cone give Hom(P[n],cone) = 0. Compact generation in lemma-hypotheses-brown-representability
   makes the cone zero (the argument of lemma-hypotheses-brown-representability, whose
   statement specializes to the finite-field setting). Then
   theorem-existence-exceptional-inverse-image makes the comparison invertible. This includes
   the empty family, so all small coproducts are preserved.
-/
theorem exists_localizingExceptionalAdjoint
    (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (hcd : AlgebraicGeometry.ProEtale.BaseFieldFiniteCD ℓ k)
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (c : Compactification.BoundaryCompactification f)
    (_hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) :
    ∃ (h : ∀ K, localizingClosureProEtale Λ X K → localizingClosureProEtale Λ Y
          ((rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K))
      (hX : (localizingClosureProEtale Λ X).IsTriangulated)
      (hY : (localizingClosureProEtale Λ Y).IsTriangulated),
      (fun [triX : (localizingClosureProEtale Λ X).IsTriangulated]
          [triY : (localizingClosureProEtale Λ Y).IsTriangulated] ↦
        (localizingLowerShriek Λ c.obj.obj h).IsTriangulated ∧
        Nonempty (HasCoproducts.{u + 1} (localizingClosureProEtale Λ X).FullSubcategory) ∧
        Nonempty (HasCoproducts.{u + 1} (localizingClosureProEtale Λ Y).FullSubcategory) ∧
        (∀ I : Type (u + 1),
          PreservesColimitsOfShape (Discrete I) (localizingLowerShriek Λ c.obj.obj h)) ∧
        ∃ G : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
            (localizingClosureProEtale Λ X).FullSubcategory,
          ∃ s : G.CommShift ℤ,
            (fun [comm : G.CommShift ℤ] ↦
              G.IsTriangulated ∧
              (∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) G) ∧
              ∃ adj : localizingLowerShriek Λ c.obj.obj h ⊣ G,
                ∀ (J : (localizingClosureProEtale Λ Y).FullSubcategory ⥤
                    (localizingClosureProEtale Λ X).FullSubcategory)
                  (adjJ : localizingLowerShriek Λ c.obj.obj h ⊣ J),
                  ∃! e : G ≅ J, ∀ N,
                    (localizingLowerShriek Λ c.obj.obj h).map (e.hom.app N) ≫
                      adjJ.counit.app N = adj.counit.app N)
              (comm := s))
        (triX := hX) (triY := hY) := by
  classical
  let hBX := brownHypotheses ℓ (ringChar k) (Fact.out : (ringChar k).Prime).pos
    (Fact.out : ringChar k ≠ ℓ) hcd (X ↘ Spec (.of k)) Λ _hΛ
  let hBY := brownHypotheses ℓ (ringChar k) (Fact.out : (ringChar k).Prime).pos
    (Fact.out : ringChar k ≠ ℓ) hcd (Y ↘ Spec (.of k)) Λ _hΛ
  obtain ⟨hsmallX, hX, hrepX, hSX, hisoSX, hretX, hessX, hidX, hsumX, hgenX⟩ := hBX
  obtain ⟨hsmallY, hY, hrepY, hSY, hisoSY, hretY, hessY, hidY, hsumY, hgenY⟩ := hBY
  let := hX
  let := hY
  -- Fix the shift before instance search, and reuse the resulting families below.
  have : ∀ n : ℤ,
      (shiftFunctor (localizingClosureProEtale Λ X).FullSubcategory n).Additive :=
    fun n ↦ inferInstance
  have : ∀ n : ℤ,
      (shiftFunctor (localizingClosureProEtale Λ Y).FullSubcategory n).Additive :=
    fun n ↦ inferInstance
  let := hsmallX
  let := hsmallY
  let := hrepX
  let := hrepY
  let := hsumX
  let := hsumY
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace (Y ↘ Spec (.of k))
  let : QuasiSeparatedSpace Y :=
    quasiSeparatedSpace_of_quasiSeparated (Y ↘ Spec (.of k))
  obtain ⟨h, hexact, hsums, hctf⟩ := compactification_localizing Λ ℓ k f c _hΛ
  refine ⟨h, hX, hY, ?_⟩
  let F := localizingLowerShriek Λ c.obj.obj h
  have hFtri : F.IsTriangulated := by
    dsimp [F, localizingLowerShriek]
    infer_instance
  let := hFtri
  let SX := constantModelBoundedConstructible Λ X ⊓ fun K ↦
    DerivedCategory.finiteTorAmplitude _ K
  obtain ⟨hambientX, _, _, hlocalX, _, _, _, _⟩ := localizingClosure_exists Λ X SX
  let := hambientX
  have hclosedBig (I : Type (u + 2)) :
      (localizingClosureProEtale Λ X).IsClosedUnderColimitsOfShape (Discrete I) :=
    hlocalX.isClosedUnderColimitsOfShape_discrete I
  have hFsums : ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) F := by
    intro I
    let eI := Discrete.equivalence (Equiv.ulift : ULift.{u + 2} I ≃ I)
    let := hclosedBig (ULift.{u + 2} I)
    let : (localizingClosureProEtale Λ X).IsClosedUnderColimitsOfShape (Discrete I) :=
      ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence eI
    have hcomp : PreservesColimitsOfShape (Discrete I)
        ((localizingClosureProEtale Λ X).ι ⋙
          rightDerivedLowerShriekOfCompactification Λ c.obj.obj) := by
      constructor
      intro K
      have hpres : PreservesColimit (K ⋙ (localizingClosureProEtale Λ X).ι)
          (rightDerivedLowerShriekOfCompactification Λ c.obj.obj) := by
        let H := K ⋙ (localizingClosureProEtale Λ X).ι
        let := hsums (ULift.{u + 2} I) (eI.functor ⋙ H)
          (fun i ↦ (K.obj (eI.functor.obj (Discrete.mk i))).property)
        exact Functor.Final.preservesColimit_of_comp eI.functor
      let := hpres
      infer_instance
    have : PreservesColimitsOfShape (Discrete I)
        (F ⋙ (localizingClosureProEtale Λ Y).ι) := by
      let := hcomp
      exact preservesColimitsOfShape_of_natIso
        ((localizingClosureProEtale Λ Y).liftCompιIso _ _).symm
    exact preservesColimitsOfShape_of_reflects_of_preserves F
      (localizingClosureProEtale Λ Y).ι
  obtain ⟨IX, hIX, ⟨eX⟩⟩ := (ObjectProperty.exists_equivalence_iff SX).mpr hessX
  let := hIX
  let e := eX.symm
  have hLX : ∀ i : IX, localizingClosureProEtale Λ X (e.functor.obj i).obj := by
    intro i P hP hSP
    exact hSP _ (e.functor.obj i).property
  obtain ⟨hcompactX, hgenerateX⟩ := hgenX IX e hLX
  have hC : IsCompactlyGeneratedTriangulated.{u + 1}
      (localizingClosureProEtale Λ X).FullSubcategory :=
    ⟨IX, _, hcompactX, hgenerateX⟩
  have hleft : F.IsLeftAdjoint := by
    apply Functor.isLeftAdjoint_of_rightAdjointObjIsDefined_eq_top
    funext N
    apply propext
    exact ⟨fun _ ↦ trivial, fun _ ↦
      brownHomRepresentabilityLocallySmall F hC hFsums N⟩
  let := hleft
  let G := F.rightAdjoint
  let adj : F ⊣ G := Adjunction.ofIsLeftAdjoint F
  let s : G.CommShift ℤ := adj.rightAdjointCommShift ℤ
  let := s
  let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  have hGtri : G.IsTriangulated := adj.isTriangulated_rightAdjoint
  have hcompactAllX (K : (localizingClosureProEtale Λ X).FullSubcategory)
      (hK : SX K.obj) : IsCompactObject K := by
    let i := e.inverse.obj ⟨K.obj, hK⟩
    let ei := e.counitIso.app ⟨K.obj, hK⟩
    let q : K ≅ (⟨(e.functor.obj i).obj, hLX i⟩ :
        (localizingClosureProEtale Λ X).FullSubcategory) :=
      (localizingClosureProEtale Λ X).fullyFaithfulι.preimageIso
        (SX.ι.mapIso ei).symm
    exact compact_of_iso q (hcompactX i)
  let SY := constantModelBoundedConstructible Λ Y ⊓ fun K ↦
    DerivedCategory.finiteTorAmplitude _ K
  obtain ⟨IY, hIY, ⟨eY'⟩⟩ := (ObjectProperty.exists_equivalence_iff SY).mpr hessY
  let := hIY
  let eY := eY'.symm
  have hSYL : SY ≤ localizingClosureProEtale Λ Y := by
    intro K hK P hP hSP
    exact hSP K hK
  have hLY : ∀ i : IY, localizingClosureProEtale Λ Y (eY.functor.obj i).obj :=
    fun i ↦ hSYL _ (eY.functor.obj i).property
  obtain ⟨hcompactY, _⟩ := hgenY IY eY hLY
  have hcompactAllY (K : (localizingClosureProEtale Λ Y).FullSubcategory)
      (hK : SY K.obj) : IsCompactObject K := by
    let i := eY.inverse.obj ⟨K.obj, hK⟩
    let ei := eY.counitIso.app ⟨K.obj, hK⟩
    let q : K ≅ (⟨(eY.functor.obj i).obj, hLY i⟩ :
        (localizingClosureProEtale Λ Y).FullSubcategory) :=
      (localizingClosureProEtale Λ Y).fullyFaithfulι.preimageIso
        (SY.ι.mapIso ei).symm
    exact compact_of_iso q (hcompactY i)
  let E : IX → (localizingClosureProEtale Λ X).FullSubcategory :=
    fun i ↦ ⟨(e.functor.obj i).obj, hLX i⟩
  let tests : IX × ULift.{u + 1} ℤ → (localizingClosureProEtale Λ X).FullSubcategory :=
    fun i ↦ (E i.1) ⟦i.2.down⟧
  have htestctf (i : IX × ULift.{u + 1} ℤ) : SX (tests i).obj := by
    let : SX.IsTriangulated := hSX
    let : SX.IsClosedUnderIsomorphisms := hisoSX
    exact SX.prop_of_iso
      (((localizingClosureProEtale Λ X).ι.commShiftIso i.2.down).app (E i.1)).symm
      (ObjectProperty.le_shift SX i.2.down _ (e.functor.obj i.1).property)
  have htests : ∀ i, IsCompactObject (tests i) ∧ IsCompactObject (F.obj (tests i)) := by
    intro i
    exact ⟨hcompactAllX _ (htestctf i), hcompactAllY _ (hctf _ (htestctf i))⟩
  have hdetect : ∀ (A B : (localizingClosureProEtale Λ X).FullSubcategory) (g : A ⟶ B),
      (∀ i, Function.Bijective (fun a : tests i ⟶ A ↦ a ≫ g)) → IsIso g := by
    intro A B g hg
    exact generators_detect_iso E hgenerateX g (fun i n ↦ hg (i, ⟨n⟩))
  have hGsums : ∀ I : Type (u + 1), PreservesColimitsOfShape (Discrete I) G :=
    compactTests_rightAdjoint_preservesCoproducts F G adj _ tests htests hdetect
  refine ⟨hFtri, ⟨hsumX⟩, ⟨hsumY⟩, hFsums, G, s, hGtri, hGsums, adj, ?_⟩
  intro J adjJ
  refine ⟨adj.rightAdjointUniq adjJ, ?_, ?_⟩
  · intro N
    exact adj.rightAdjointUniq_hom_app_counit adjJ N
  · intro e he
    apply Iso.ext
    apply NatTrans.ext
    funext N
    apply (adjJ.homEquiv _ _).symm.injective
    exact (he N).trans (adj.rightAdjointUniq_hom_app_counit adjJ N).symm

end AlgebraicGeometry.ProEtale.CondensedRing
