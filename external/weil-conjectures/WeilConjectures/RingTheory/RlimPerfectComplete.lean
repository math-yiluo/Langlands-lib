/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.RingTheory.DerivedCompleteModuleComplex
import WeilConjectures.Algebra.Homology.RingPseudoCoherentSummand
import WeilConjectures.Algebra.Homology.TensorRestrictExtendScalarsModule
import WeilConjectures.RingTheory.NilpotentTorsionDerivedLimitComplete
import WeilConjectures.RingTheory.PseudoCoherentInverseRingReconstruction
import WeilConjectures.RingTheory.PseudoCoherentMaximalFibrePerfect
import WeilConjectures.RingTheory.PseudoCoherentNormalizedAlgebraTower

/-!
# Perfect inverse-limit reconstruction over a complete ring

Source: Stacks Project, More on Algebra, Tag 09AW, lemma-Rlim-perfect-gives-complete
(auxiliary; not a blueprint node).

The index `n : ℕ` denotes level `n + 1`. Derived scalar extension is specified by its
universal property as the left adjoint to exact restriction of scalars. We allow any
realization of this adjunction; all maps below are its adjoint transposes, so no arbitrary
comparison map is supplied. The derived limit includes its Roos triangle and projections.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace DerivedCategory

/-- Exact restriction from the `(n+1)`st quotient to the complete ring.
Source: Stacks Project, Tag 09AW
(auxiliary; not a blueprint node). -/
noncomputable def adicLevelRestriction {A : Type u} [CommRing A] (I : Ideal A)
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [∀ n : ℕ, HasDerivedCategory.{u} (ModuleCat.{u} (A ⧸ I ^ (n + 1)))] (n : ℕ) :
    DerivedCategory (ModuleCat.{u} (A ⧸ I ^ (n + 1))) ⥤
      DerivedCategory (ModuleCat.{u} A) :=
  (ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ (n + 1)))).mapDerivedCategory

/-- Exact restriction between consecutive quotient rings.
Source: Stacks Project, Tag 09AW
(auxiliary; not a blueprint node). -/
noncomputable def adicStepRestriction {A : Type u} [CommRing A] (I : Ideal A)
    [∀ n : ℕ, HasDerivedCategory.{u} (ModuleCat.{u} (A ⧸ I ^ (n + 1)))] (n : ℕ) :
    DerivedCategory (ModuleCat.{u} (A ⧸ I ^ (n + 1))) ⥤
      DerivedCategory (ModuleCat.{u} (A ⧸ I ^ (n + 1 + 1))) :=
  (ModuleCat.restrictScalars (Ideal.Quotient.factorPowSucc I (n + 1))).mapDerivedCategory

/-- The canonical identification of iterated restriction with direct restriction.
Source: Stacks Project, Tag 09AW; both underived maps send every element to itself.
(auxiliary; not a blueprint node). -/
noncomputable def adicRestrictionComp {A : Type u} [CommRing A] (I : Ideal A)
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [∀ n : ℕ, HasDerivedCategory.{u} (ModuleCat.{u} (A ⧸ I ^ (n + 1)))] (n : ℕ) :
    adicLevelRestriction I n ≅ adicStepRestriction I n ⋙ adicLevelRestriction I (n + 1) :=
  Functor.mapDerivedCategoryNatIso
    (ModuleCat.restrictScalarsComp'
      (Ideal.Quotient.mk (I ^ (n + 1 + 1)))
      (Ideal.Quotient.factorPowSucc I (n + 1))
      (Ideal.Quotient.mk (I ^ (n + 1)))
      (Ideal.Quotient.factor_comp_mk (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))).symm) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- Restrict a supplied transition in `D(A/I^(n+2))` to `D(A)`.
Source: Stacks Project, Tag 09AW
(auxiliary; not a blueprint node). -/
noncomputable def adicTowerTransition {A : Type u} [CommRing A] (I : Ideal A)
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [∀ n : ℕ, HasDerivedCategory.{u} (ModuleCat.{u} (A ⧸ I ^ (n + 1)))]
    (K : ∀ n : ℕ, DerivedCategory (ModuleCat.{u} (A ⧸ I ^ (n + 1))))
    (t : ∀ n : ℕ, K (n + 1) ⟶ (adicStepRestriction I n).obj (K n)) (n : ℕ) :
    (adicLevelRestriction I (n + 1)).obj (K (n + 1)) ⟶
      (adicLevelRestriction I n).obj (K n) :=
  (adicLevelRestriction I (n + 1)).map (t n) ≫ (adicRestrictionComp I n).inv.app (K n)

/-- The canonical reduction map: transpose the projection of the specified Roos triangle.
Source: Stacks Project, Tag 09AW
(auxiliary; not a blueprint node). -/
noncomputable def adicLimitReduction {A : Type u} [CommRing A] (I : Ideal A)
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [∀ n : ℕ, HasDerivedCategory.{u} (ModuleCat.{u} (A ⧸ I ^ (n + 1)))]
    (K : ∀ n : ℕ, DerivedCategory (ModuleCat.{u} (A ⧸ I ^ (n + 1))))
    [HasProduct (fun n : ℕ ↦ (adicLevelRestriction I n).obj (K n))]
    (L : ∀ n : ℕ, DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} (A ⧸ I ^ (n + 1))))
    (adj : ∀ n : ℕ, L n ⊣ adicLevelRestriction I n)
    (C : DerivedCategory (ModuleCat.{u} A))
    (p : C ⟶ ∏ᶜ (fun n : ℕ ↦ (adicLevelRestriction I n).obj (K n))) (n : ℕ) :
    (L n).obj C ⟶ K n :=
  ((adj n).homEquiv C (K n)).symm (p ≫ Pi.π _ n)

private theorem smul_id_derived_restriction_eq_zero
    {R S : Type u} [CommRing R] [CommRing S]
    [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    [HasDerivedCategory.{u} (ModuleCat.{u} S)]
    (f : R →+* S) (r : R) (hr : f r = 0)
    (X : DerivedCategory (ModuleCat.{u} S)) :
    r • 𝟙 ((ModuleCat.restrictScalars f).mapDerivedCategory.obj X) = 0 := by
  classical
  let P := Q.objPreimage X
  let F := ModuleCat.restrictScalars f
  let e : F.mapDerivedCategory.obj X ≅ Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P) :=
    F.mapDerivedCategory.mapIso (Q.objObjPreimageIso X).symm ≪≫
      F.mapDerivedCategoryFactors.app P
  have hz : r • 𝟙 ((F.mapHomologicalComplex (.up ℤ)).obj P) = 0 := by
    ext i x
    change r • x = (0 : (ModuleCat.restrictScalars f).obj (P.X i))
    rw [ModuleCat.restrictScalars.smul_def, hr, zero_smul]
  have hzQ : r • 𝟙 (Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) = 0 := by
    rw [← Q.map_id, ← Functor.map_smul, hz, Q.map_zero]
  apply (cancel_mono e.hom).1
  calc
    (r • 𝟙 _) ≫ e.hom = e.hom ≫ (r • 𝟙 _) := by
      simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
    _ = 0 ≫ e.hom := by rw [hzQ, comp_zero, zero_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem isPseudoCoherent_of_isPerfect
    {R : Type u} [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    {X : DerivedCategory (ModuleCat.{u} R)} (hX : IsPerfect X) : IsPseudoCoherent X := by
  classical
  obtain ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩ := hX
  have : P.IsStrictlyLE b := hb
  have splits (i : ℤ) : ∃ n : ℕ, (b < i → n = 0) ∧
      ∃ (f : ModuleCat.of R (Fin n → R) ⟶ P.X i)
        (g : P.X i ⟶ ModuleCat.of R (Fin n → R)), g ≫ f = 𝟙 _ := by
    by_cases hi : b < i
    · refine ⟨0, fun _ ↦ rfl, 0, 0, ?_⟩
      exact (P.isZero_of_isStrictlyLE b i hi).eq_of_src _ _
    · have := (hP i).1
      have := (hP i).2
      obtain ⟨n, f, g, _, _, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R (P.X i)
      refine ⟨n, fun h ↦ (hi h).elim, ModuleCat.ofHom f, ModuleCat.ofHom g, ?_⟩
      exact ModuleCat.hom_ext hfg
  choose n hn f g hgf using splits
  let F : CochainComplex (ModuleCat.{u} R) ℤ :=
    { X := fun i ↦ ModuleCat.of R (Fin (n i) → R)
      d := fun i j ↦ f i ≫ P.d i j ≫ g j
      shape := fun i j hij ↦ by rw [P.shape i j hij, zero_comp, comp_zero]
      d_comp_d' := fun i j k _ _ ↦ by
        simp only [Category.assoc]
        rw [← Category.assoc (g j), hgf j, Category.id_comp,
          ← Category.assoc (P.d i j), P.d_comp_d, zero_comp, comp_zero] }
  have hFb : F.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    change IsZero (ModuleCat.of R (Fin (n i) → R))
    rw [hn i hi]
    exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance
  let inc : P ⟶ F :=
    { f := g
      comm' := fun i j _ ↦ by
        dsimp [F]
        rw [← Category.assoc, hgf i, Category.id_comp] }
  let ret : F ⟶ P :=
    { f := f
      comm' := fun i j _ ↦ by
        dsimp [F]
        rw [Category.assoc, Category.assoc, hgf j, Category.comp_id] }
  have hret : inc ≫ ret = 𝟙 P := by
    apply HomologicalComplex.hom_ext
    intro i
    exact hgf i
  have hs : Q.map inc ≫ Q.map ret = 𝟙 _ := by
    rw [← Q.map_comp, hret, Q.map_id]
  have : IsSplitMono (Q.map inc) := ⟨⟨Q.map ret, hs⟩⟩
  obtain ⟨Z, v, w, hT⟩ := Pretriangulated.distinguished_cocone_triangle (Q.map inc)
  let T := Pretriangulated.Triangle.mk (Q.map inc) v w
  have hz : T.mor₃ = 0 :=
    Pretriangulated.Triangle.mor₃_eq_zero_of_mono₁ T hT
      (inferInstanceAs (Mono (Q.map inc)))
  obtain ⟨eF, _, _⟩ := Pretriangulated.exists_iso_binaryBiproduct_of_distTriang T hT hz
  have hsum : IsPseudoCoherent (Q.obj P ⊞ Z) :=
    ⟨F, b, hFb, fun i ↦ ⟨inferInstance, inferInstance⟩, ⟨eF⟩⟩
  obtain ⟨E, c, hEc, hE, ⟨eE⟩⟩ := (pseudoCoherent_summand (Q.obj P) Z hsum).1
  exact ⟨E, c, hEc, hE, ⟨eE ≪≫ e.symm⟩⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem tensorBaseChangeIso
    {R S : Type u} [CommRing R] [CommRing S] (q : R →+* S)
    (N : ModuleCat.{u} S) :
    Nonempty (ModuleCat.extendScalars q ⋙ tensorRight N ⋙ ModuleCat.restrictScalars q ≅
      tensorRight ((ModuleCat.restrictScalars q).obj N)) := by
  obtain ⟨e, he⟩ := ModuleCat.exists_tensorRestrictExtend_module_natural q
  let eL : ModuleCat.extendScalars q ⋙ tensorLeft N ⋙ ModuleCat.restrictScalars q ≅
      tensorLeft ((ModuleCat.restrictScalars q).obj N) :=
    NatIso.ofComponents (fun M ↦ e N M) (by
      intro M M' g
      change (ModuleCat.restrictScalars q).map
          (N ◁ (ModuleCat.extendScalars q).map g) ≫ (e N M').hom =
        (e N M).hom ≫ (ModuleCat.restrictScalars q).obj N ◁ g
      simpa only [(ModuleCat.restrictScalars q).map_id, id_tensorHom] using
        he N N M M' (𝟙 _) g)
  exact ⟨Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (ModuleCat.extendScalars q)
        (BraidedCategory.tensorLeftIsoTensorRight N).symm)
      (ModuleCat.restrictScalars q) ≪≫ eL ≪≫
        BraidedCategory.tensorLeftIsoTensorRight _⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem tensor_bound_of_perfect_scalar_model
    {A S : Type u} [CommRing A] [CommRing S]
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [HasDerivedCategory.{u} (ModuleCat.{u} S)]
    (q : A →+* S)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (bP : ℤ) [P.IsStrictlyLE bP]
    (hP : ∀ i, Module.Flat A (P.X i))
    (P₀ : CochainComplex (ModuleCat.{u} S) ℤ) (b₀ : ℤ) [P₀.IsStrictlyLE b₀]
    (hP₀ : ∀ i, Module.Flat S (P₀.X i))
    (θ : ((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj P ≅ P₀)
    (hperfect : IsPerfect (Q.obj P₀)) :
    ∃ a b : ℤ, a ≤ b ∧ ∀ (N : ModuleCat.{u} S) (i : ℤ), (i < a ∨ b < i) →
      IsZero ((homologyFunctor (ModuleCat.{u} A) i).obj
        (Q.obj P ⊗ (singleFunctor (ModuleCat.{u} A) 0).obj
          ((ModuleCat.restrictScalars q).obj N))) := by
  classical
  obtain ⟨T, a, b, hTa, hTb, hT, ⟨eT⟩⟩ := hperfect
  have : T.IsStrictlyGE a := hTa
  have : T.IsStrictlyLE b := hTb
  have htor := torAmplitudeIn_Q_obj_of_flat T a b fun i ↦ by
    have := (hT i).1
    exact (ModuleCat.flat_iff_flat _).2 inferInstance
  have hPk := CochainComplex.kFlat_of_isStrictlyLE_of_flat P bP
    (fun i ↦ (ModuleCat.flat_iff_flat _).2 (hP i))
  have hP₀k := CochainComplex.kFlat_of_isStrictlyLE_of_flat P₀ b₀
    (fun i ↦ (ModuleCat.flat_iff_flat _).2 (hP₀ i))
  refine ⟨min a b, b, min_le_right _ _, ?_⟩
  intro N i hi
  have hzero : IsZero ((homologyFunctor (ModuleCat.{u} S) i).obj
      (Q.obj P₀ ⊗ (singleFunctor (ModuleCat.{u} S) 0).obj N)) := by
    have hbnd := htor N
    have : (Q.obj T ⊗ (singleFunctor (ModuleCat.{u} S) 0).obj N).IsGE a := hbnd.1
    have : (Q.obj T ⊗ (singleFunctor (ModuleCat.{u} S) 0).obj N).IsLE b := hbnd.2
    have e := whiskerRightIso eT ((singleFunctor (ModuleCat.{u} S) 0).obj N)
    apply IsZero.of_iso _ ((homologyFunctor (ModuleCat.{u} S) i).mapIso e)
    rcases hi with hi | hi
    · exact isZero_of_isGE _ a i (lt_of_lt_of_le hi (min_le_left _ _))
    · exact isZero_of_isLE _ b i hi
  let res := ModuleCat.restrictScalars q
  let TP := ((tensorRight (res.obj N)).mapHomologicalComplex (.up ℤ)).obj P
  let T₀ := ((tensorRight N).mapHomologicalComplex (.up ℤ)).obj P₀
  obtain ⟨e⟩ := tensorBaseChangeIso q N
  let eC : ((res.mapHomologicalComplex (.up ℤ)).obj T₀) ≅ TP :=
    (res.mapHomologicalComplex (.up ℤ)).mapIso
      (((tensorRight N).mapHomologicalComplex (.up ℤ)).mapIso θ.symm) ≪≫
        (NatIso.mapHomologicalComplex e (.up ℤ)).app P
  have hz₀ : IsZero ((homologyFunctor (ModuleCat.{u} S) i).obj (Q.obj T₀)) :=
    hzero.of_iso ((homologyFunctor (ModuleCat.{u} S) i).mapIso
      (QObjTensorSingleFunctorObjIso P₀ hP₀k N)).symm
  have hzres : IsZero ((homologyFunctor (ModuleCat.{u} A) i).obj
      (res.mapDerivedCategory.obj (Q.obj T₀))) :=
    (res.map_isZero hz₀).of_iso ((res.mapDerivedCategoryHomologyFunctorIso i).app
      (Q.obj T₀)).symm
  let eD : res.mapDerivedCategory.obj (Q.obj T₀) ≅ Q.obj TP :=
    res.mapDerivedCategoryFactors.app T₀ ≪≫ Q.mapIso eC
  exact hzres.of_iso
    ((homologyFunctor (ModuleCat.{u} A) i).mapIso
      (QObjTensorSingleFunctorObjIso P hPk (res.obj N) ≪≫ eD.symm))

/-- The two bounded-above flat models needed for the residue-field argument.
Keeping these fields in a record avoids repeatedly specializing reconstruction's much larger
witness statement. Source: Stacks Project, Tag 0CQF
(auxiliary; not a blueprint node). -/
private structure ScalarReductionModel {A S : Type u} [CommRing A] [CommRing S]
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [HasDerivedCategory.{u} (ModuleCat.{u} S)]
    (q : A →+* S) (C : DerivedCategory (ModuleCat.{u} A))
    (C₀ : DerivedCategory (ModuleCat.{u} S)) where
  P : CochainComplex (ModuleCat.{u} A) ℤ
  P₀ : CochainComplex (ModuleCat.{u} S) ℤ
  b : ℤ
  bounded : P.IsStrictlyLE b
  bounded₀ : P₀.IsStrictlyLE b
  flat : ∀ i, Module.Flat A (P.X i)
  flat₀ : ∀ i, Module.Flat S (P₀.X i)
  marking : Q.obj P ≅ C
  marking₀ : Q.obj P₀ ≅ C₀
  reduction : ((ModuleCat.extendScalars q).mapHomologicalComplex (.up ℤ)).obj P ≅ P₀

set_option backward.isDefEq.respectTransparency false in
/-- Project the existing generic reconstruction onto its scalar-reduction model interface,
before specializing the rings. This forgets transition and normalization data already used
inside reconstruction, while retaining the two marked flat models and their reduction.
Source: Stacks Project, Tag 0CQF
(auxiliary; not a blueprint node). -/
private theorem reconstruction_scalar_model
    (R : ℕ → Type u) [∀ n, CommRing (R n)]
    (φ : ∀ n, R (n + 1) →+* R n)
    (hsurj : ∀ n, Function.Surjective (φ n))
    (hnil : ∀ n, IsNilpotent (RingHom.ker (φ n)))
    (A : Type u) [CommRing A] (q : ∀ n, A →+* R n)
    (hq : ∀ n, q n = (φ n).comp (q (n + 1)))
    (hlim : ∀ x : ∀ n, R n, (∀ n, φ n (x (n + 1)) = x n) →
      ∃! a : A, ∀ n, q n a = x n)
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [∀ n, HasDerivedCategory.{u} (ModuleCat.{u} (R n))]
    (L : ∀ n, DerivedCategory (ModuleCat.{u} (R (n + 1))) ⥤
      DerivedCategory (ModuleCat.{u} (R n)))
    (adjφ : ∀ n, L n ⊣ (ModuleCat.restrictScalars (φ n)).mapDerivedCategory)
    (M : ∀ n, DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} (R n)))
    (adjq : ∀ n, M n ⊣ (ModuleCat.restrictScalars (q n)).mapDerivedCategory)
    (χ : ∀ n, (ModuleCat.restrictScalars (q n)).mapDerivedCategory ≅
      (ModuleCat.restrictScalars (φ n)).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory)
    (hχ : ∀ n (C : CochainComplex (ModuleCat.{u} (R n)) ℤ),
      (χ n).hom.app (Q.obj C) ≫
        (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory.map
          ((ModuleCat.restrictScalars (φ n)).mapDerivedCategoryFactors.hom.app C) ≫
        (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.restrictScalars (φ n)).mapHomologicalComplex (.up ℤ)).obj C) =
      (ModuleCat.restrictScalars (q n)).mapDerivedCategoryFactors.hom.app C ≫
        Q.map ((NatIso.mapHomologicalComplex
          (ModuleCat.restrictScalarsComp' (q (n + 1)) (φ n) (q n) (hq n))
          (.up ℤ)).hom.app C))
    (Eₙ : ∀ n, DerivedCategory (ModuleCat.{u} (R n)))
    (t : ∀ n, Eₙ (n + 1) ⟶
      (ModuleCat.restrictScalars (φ n)).mapDerivedCategory.obj (Eₙ n))
    (hred : ∀ n, IsIso (((adjφ n).homEquiv (Eₙ (n + 1)) (Eₙ n)).symm (t n)))
    (hpc : IsPseudoCoherent (Eₙ 0))
    [HasProduct (fun n ↦ (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (Eₙ n))]
    (E : DerivedCategory (ModuleCat.{u} A))
    (pE : E ⟶ ∏ᶜ fun n ↦
      (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (Eₙ n))
    (δ : (∏ᶜ fun n ↦ (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj (Eₙ n)) ⟶
      E⟦(1 : ℤ)⟧)
    (hE : IsDerivedLimitTriangle
      (fun n ↦ (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory.map (t n) ≫
        (χ n).inv.app (Eₙ n)) E pE δ) :
    IsPseudoCoherent E ∧
      (∀ n, IsIso (((adjq n).homEquiv E (Eₙ n)).symm (pE ≫ Pi.π _ n))) ∧
      Nonempty (ScalarReductionModel (q 0) E (Eₙ 0)) := by
  classical
  have hr := isPseudoCoherent_inverse_ring_reconstruction R φ hsurj hnil A q hq hlim
    L adjφ M adjq χ hχ Eₙ t hred hpc E pE δ hE
  refine ⟨hr.1, hr.2.1, ?_⟩
  obtain ⟨Pₙ, c, βₙ, uₙ, θₙ, P, β, pr, θ, η, γ, h⟩ := hr.2.2
  refine ⟨⟨P, Pₙ 0, c, h.2.2.2.2.2.1, h.1 0, ?_, ?_, β, βₙ 0, θ 0⟩⟩
  · intro i
    have := (h.2.2.2.2.2.2.1 i).1
    infer_instance
  · intro i
    have := (h.2.1 0 i).1
    infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- Perfect compatible reductions reconstruct a perfect, derived complete object, and its
projection-induced reductions are isomorphisms compatible with the transition maps.
Source: Stacks Project, More on Algebra, Tag 09AW
(auxiliary; not a blueprint node).

Proof:
1. Represent `K 0` by a bounded finite-projective complex and retract each term from a
   finite free module, choosing rank zero above the bound. Transfer the differential using
   these retractions. This gives a chain retract of a bounded-above finite-free complex.
   A split triangle and `lem-pc-ring-pseudo-coherent-summand` give pseudo-coherence.
2. The quotient transitions are surjective with square-zero kernels. Completeness identifies
   their inverse limit with `A`. Apply `lem-weil-pbc-pseudocoherent-inverse-ring-reconstruction`
   to obtain compatible finite-free models and a bounded-above finite-free limit model,
   with projection-induced reduction isomorphisms. In particular the limit is pseudo-coherent.
3. Every maximal ideal contains `I` by `lem-weil-pbc-adic-complete-jacobson-radical`.
   The existing source K-flat single-module tensor comparison, the ordinary natural
   tensor/restriction comparison, and exact restriction of scalars identify homology with
   that of `K 0` tensored with the residue module. A bounded finite-projective model of
   `K 0` therefore supplies one interval bounding all residue-field cohomologies.
4. Apply `lem-weil-pbc-pseudocoherent-maximal-fibre-perfect` to conclude perfectness.
5. For `f ∈ I`, multiplication by `f^(n+1)` on the restricted `K n` is zero. Apply
   `lem-weil-pbc-nilpotent-torsion-derived-limit-complete` to obtain derived completeness
   in the vanishing sense of `def-weil-point-derived-complete-module-complex`.
6. The first two arrows of the Roos triangle compose to zero, so `p (1 - shift) = 0`.
   Composing with each product projection gives compatibility of the projections. The
   adjunction unit formula identifies them with the transposes defining
   `adicLimitReduction`, which proves exactly the displayed compatibility. -/
theorem rlim_perfect_complete {A : Type u} [CommRing A] (I : Ideal A)
    [IsAdicComplete I A]
    [HasDerivedCategory.{u} (ModuleCat.{u} A)]
    [∀ n : ℕ, HasDerivedCategory.{u} (ModuleCat.{u} (A ⧸ I ^ (n + 1)))]
    (K : ∀ n : ℕ, DerivedCategory (ModuleCat.{u} (A ⧸ I ^ (n + 1))))
    (t : ∀ n : ℕ, K (n + 1) ⟶ (adicStepRestriction I n).obj (K n))
    (L : ∀ n : ℕ, DerivedCategory (ModuleCat.{u} A) ⥤
      DerivedCategory (ModuleCat.{u} (A ⧸ I ^ (n + 1))))
    (adj : ∀ n : ℕ, L n ⊣ adicLevelRestriction I n)
    (B : ∀ n : ℕ, DerivedCategory (ModuleCat.{u} (A ⧸ I ^ (n + 1 + 1))) ⥤
      DerivedCategory (ModuleCat.{u} (A ⧸ I ^ (n + 1))))
    (badj : ∀ n : ℕ, B n ⊣ adicStepRestriction I n)
    (hbase : ∀ n : ℕ, IsIso (((badj n).homEquiv (K (n + 1)) (K n)).symm (t n)))
    (hperfect : IsPerfect (K 0))
    [HasProduct (fun n : ℕ ↦ (adicLevelRestriction I n).obj (K n))]
    (C : DerivedCategory (ModuleCat.{u} A))
    (p : C ⟶ ∏ᶜ (fun n : ℕ ↦ (adicLevelRestriction I n).obj (K n)))
    (δ : ∏ᶜ (fun n : ℕ ↦ (adicLevelRestriction I n).obj (K n)) ⟶ C⟦(1 : ℤ)⟧)
    (hlim : IsDerivedLimitTriangle (adicTowerTransition I K t) C p δ) :
    IsPerfect C ∧ IsDerivedComplete I C ∧
      (∀ n : ℕ, IsIso (adicLimitReduction I K L adj C p n)) ∧
      ∀ n : ℕ,
        (adj (n + 1)).unit.app C ≫
            (adicLevelRestriction I (n + 1)).map (adicLimitReduction I K L adj C p (n + 1)) ≫
            adicTowerTransition I K t n =
          (adj n).unit.app C ≫
            (adicLevelRestriction I n).map (adicLimitReduction I K L adj C p n)  := by
  classical
  have hpc₀ : IsPseudoCoherent (K 0) := isPseudoCoherent_of_isPerfect hperfect
  let R (n : ℕ) := A ⧸ I ^ (n + 1)
  let φ (n : ℕ) : R (n + 1) →+* R n := Ideal.Quotient.factorPowSucc I (n + 1)
  let q (n : ℕ) : A →+* R n := Ideal.Quotient.mk (I ^ (n + 1))
  have hq (n : ℕ) : q n = (φ n).comp (q (n + 1)) :=
    (Ideal.Quotient.factor_comp_mk _).symm
  have : HasProduct (fun n ↦ (ModuleCat.restrictScalars (q n)).mapDerivedCategory.obj
      (K n)) := inferInstanceAs (HasProduct (fun n ↦ (adicLevelRestriction I n).obj (K n)))
  let χ (n : ℕ) : (ModuleCat.restrictScalars (q n)).mapDerivedCategory ≅
      (ModuleCat.restrictScalars (φ n)).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory :=
    Functor.mapDerivedCategoryNatIso
      (ModuleCat.restrictScalarsComp' (q (n + 1)) (φ n) (q n) (hq n)) ≪≫
        (Functor.mapDerivedCategoryCompIso (ModuleCat.restrictScalars (φ n))
          (ModuleCat.restrictScalars (q (n + 1)))).symm
  have hχ := fun n ↦ restrictScalarsComp_derived_factors
    (q (n + 1)) (φ n) (q n) (hq n)
  have htri : IsDerivedLimitTriangle
      (fun n ↦ (ModuleCat.restrictScalars (q (n + 1))).mapDerivedCategory.map (t n) ≫
        (χ n).inv.app (K n)) C p δ := hlim
  have hr := reconstruction_scalar_model R φ
    (fun n ↦ Ideal.Quotient.factor_surjective _) (fun n ↦ adic_step_nilpotent I n)
    A q hq (adic_quotient_limit I) B badj L adj χ hχ
    K t hbase hpc₀ C p δ htri
  have hperf : IsPerfect C := by
    obtain ⟨a, b, hab, hfibres⟩ : ∃ a b : ℤ, a ≤ b ∧
        ∀ (m : Ideal A), m.IsMaximal → ∀ i : ℤ, (i < a ∨ b < i) →
          IsZero ((homologyFunctor (ModuleCat.{u} A) i).obj
            (C ⊗ (singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A (A ⧸ m)))) := by
      obtain ⟨model⟩ := hr.2.2
      have : model.P.IsStrictlyLE model.b := model.bounded
      have : model.P₀.IsStrictlyLE model.b := model.bounded₀
      obtain ⟨a, b, hab, hbound⟩ := tensor_bound_of_perfect_scalar_model (q 0)
        model.P model.b model.flat model.P₀ model.b model.flat₀ model.reduction
        (hperfect.of_iso model.marking₀.symm)
      refine ⟨a, b, hab, ?_⟩
      intro m hm i hi
      have hIm : I ^ (0 + 1) ≤ m := by
        simpa only [zero_add, pow_one] using
          (IsAdicComplete.le_jacobson_bot I).trans (sInf_le ⟨bot_le, hm⟩)
      let g : R 0 →+* A ⧸ m := Ideal.Quotient.factor hIm
      let N : ModuleCat.{u} (R 0) :=
        (ModuleCat.restrictScalars g).obj (ModuleCat.of (A ⧸ m) (A ⧸ m))
      let eκ : (ModuleCat.restrictScalars (q 0)).obj N ≅ ModuleCat.of A (A ⧸ m) :=
        ((ModuleCat.restrictScalarsComp' (q 0) g (Ideal.Quotient.mk m)
          (Ideal.Quotient.factor_comp_mk hIm).symm).app
            (ModuleCat.of (A ⧸ m) (A ⧸ m))).symm
      let eC := tensorIso model.marking.symm ((singleFunctor (ModuleCat.{u} A) 0).mapIso eκ.symm)
      exact (hbound N i hi).of_iso
        ((homologyFunctor (ModuleCat.{u} A) i).mapIso eC)
    exact (isPerfect_and_tensor_homology_vanish_of_maximal_fibres
      C hr.1 a b hab hfibres).1
  have hcomplete : IsDerivedComplete I C := by
    apply isDerivedComplete_of_isDerivedLimit_of_nilpotent I
      (fun n ↦ (adicLevelRestriction I n).obj (K n)) (adicTowerTransition I K t)
      ?_ C ⟨p, δ, hlim⟩
    intro a ha n
    refine ⟨n + 1, Nat.succ_pos n, ?_⟩
    apply smul_id_derived_restriction_eq_zero
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow ha (n + 1))
  refine ⟨hperf, hcomplete, hr.2.1, ?_⟩
  intro n
  have he (k : ℕ) : (adj k).unit.app C ≫
      (adicLevelRestriction I k).map (adicLimitReduction I K L adj C p k) =
      p ≫ Pi.π _ k := by
    exact ((adj k).homEquiv_unit C (K k) _).symm.trans
      (((adj k).homEquiv C (K k)).apply_symm_apply _)
  rw [← Category.assoc, he (n + 1), he n]
  have hz := Pretriangulated.comp_distTriang_mor_zero₁₂
    (Pretriangulated.Triangle.mk p (towerTransitionEndomorphism
      (adicTowerTransition I K t)) δ) hlim
  have hn := congrArg (fun z ↦ z ≫ Pi.π _ n) hz
  change (p ≫ towerTransitionEndomorphism (adicTowerTransition I K t)) ≫
      Pi.π (fun k ↦ (adicLevelRestriction I k).obj (K k)) n =
    (0 : C ⟶ ∏ᶜ (fun k ↦ (adicLevelRestriction I k).obj (K k))) ≫
      Pi.π (fun k ↦ (adicLevelRestriction I k).obj (K k)) n at hn
  have ht := (towerTransitionEndomorphism_eq_iff
    (K := fun n ↦ (adicLevelRestriction I n).obj (K n))
    (adicTowerTransition I K t) (towerTransitionEndomorphism
      (adicTowerTransition I K t))).mp rfl n
  have heq : p ≫ Pi.π _ n -
      p ≫ Pi.π _ (n + 1) ≫ adicTowerTransition I K t n = 0 := by
    simpa only [Category.assoc, ht, Preadditive.comp_sub, zero_comp] using hn
  simpa only [Category.assoc] using (sub_eq_zero.mp heq).symm

end DerivedCategory
