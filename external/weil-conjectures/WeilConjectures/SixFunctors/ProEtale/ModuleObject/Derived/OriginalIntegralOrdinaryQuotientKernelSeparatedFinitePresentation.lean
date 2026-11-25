/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.Topology.IntegralContinuousPresentationSeparated
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedProjective
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapCoefficientSections
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.AlgebraicGeometry.ProEtale.WContractibleDisjointCover
import WeilConjectures.NumberTheory.Padics.IntegersShrinkModPow
import WeilConjectures.NumberTheory.Padics.IntegersAlgebra
import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
import WeilConjectures.Topology.IntegralContinuousPresentationSeparated

/-! # Separation of ordinary integral quotients of finitely presented modules

The proof uses compact continuous matrix solutions on w-contractible affine tests.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry Scheme
private theorem separated_cokernel_sections
    {C : Type*} [Category C] [Abelian C] [HasFiniteBiproducts C] (P : C) [Projective P]
    {S : Type*} {R : Type} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    [ExtremallyDisconnected S] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [CompactSpace R] [T2Space R]
    [IsNoetherianRing R] [IsLocalRing R]
    (e : C(S, R) ≃+* End P) (r : ℕ) (hr : (r : R) ∈ IsLocalRing.maximalIdeal R)
    {n m : ℕ} (A : (⨁ fun _ : Fin m ↦ P) ⟶ ⨁ fun _ : Fin n ↦ P)
    (x : P ⟶ cokernel A)
    (hx : ∀ k : ℕ, x ≫ cokernel.π (r ^ k • 𝟙 (cokernel A)) = 0) : x = 0 := by
  classical
  let y := Projective.factorThru x (cokernel.π A)
  have hy : y ≫ cokernel.π A = x := Projective.factorThru_comp _ _
  let t : Matrix (Fin n) (Fin m) C(S, R) := fun i j ↦
    e.symm (.of (biproduct.ι (fun _ ↦ P) j ≫ A ≫ biproduct.π (fun _ ↦ P) i))
  let b : Fin n → C(S, R) := fun i ↦ e.symm (.of (y ≫ biproduct.π (fun _ ↦ P) i))
  have hsum {p : ℕ} {Y Z : C} (f : Y ⟶ ⨁ fun _ : Fin p ↦ P)
      (g : (⨁ fun _ : Fin p ↦ P) ⟶ Z) :
      f ≫ g = ∑ a, (f ≫ biproduct.π (fun _ ↦ P) a) ≫
        (biproduct.ι (fun _ ↦ P) a ≫ g) := by
    conv_lhs => rw [← Category.id_comp g, ← biproduct.total]
    rw [Preadditive.sum_comp, Preadditive.comp_sum]
    simp only [Category.assoc]
  have happ (z : P ⟶ ⨁ fun _ : Fin m ↦ P) (i : Fin n) :
      (e (∑ j, t i j * e.symm (.of (z ≫ biproduct.π (fun _ ↦ P) j)))).asHom =
        z ≫ A ≫ biproduct.π (fun _ ↦ P) i := by
    rw [map_sum, End.sum_asHom, hsum z (A ≫ biproduct.π (fun _ ↦ P) i)]
    apply Finset.sum_congr rfl
    intro j _
    simp only [map_mul, RingEquiv.apply_symm_apply, End.mul_asHom, t]
  have hb : ∀ k : ℕ, ∃ a : Fin m → C(S, R), ∃ c : Fin n → C(S, R),
      ∀ i, b i = (∑ j, t i j * a j) + (r : R) ^ k • c i := by
    intro k
    let d : P ⟶ cokernel A :=
      (ShortComplex.cokernelSequence_exact (r ^ k • 𝟙 (cokernel A))).liftFromProjective
        x (hx k)
    have hd : r ^ k • d = x := by
      have hd₀ := (ShortComplex.cokernelSequence_exact
        (r ^ k • 𝟙 (cokernel A))).liftFromProjective_comp x (hx k)
      change d ≫ (r ^ k • 𝟙 (cokernel A)) = x at hd₀
      simpa only [Preadditive.comp_nsmul, Category.comp_id] using hd₀
    let c := Projective.factorThru d (cokernel.π A)
    have hc : c ≫ cokernel.π A = d := Projective.factorThru_comp _ _
    have hz : (y - r ^ k • c) ≫ cokernel.π A = 0 := by
      rw [Preadditive.sub_comp, Preadditive.nsmul_comp, hy, hc, hd, sub_self]
    let z : P ⟶ ⨁ fun _ : Fin m ↦ P :=
      (ShortComplex.cokernelSequence_exact A).liftFromProjective _ hz
    have hza : z ≫ A = y - r ^ k • c :=
      (ShortComplex.cokernelSequence_exact A).liftFromProjective_comp _ hz
    refine ⟨fun j ↦ e.symm (.of (z ≫ biproduct.π (fun _ ↦ P) j)),
      fun i ↦ e.symm (.of (c ≫ biproduct.π (fun _ ↦ P) i)), fun i ↦ ?_⟩
    apply e.injective
    apply End.ext
    rw [map_add, show (r : R) ^ k • e.symm (.of (c ≫ biproduct.π (fun _ ↦ P) i)) =
      r ^ k • e.symm (.of (c ≫ biproduct.π (fun _ ↦ P) i)) by
        rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul], map_nsmul,
      End.add_asHom, End.nsmul_asHom, happ, ← Category.assoc, hza,
      Preadditive.sub_comp, Preadditive.nsmul_comp]
    simp only [b, RingEquiv.apply_symm_apply, sub_add_cancel]
  obtain ⟨a, ha⟩ := ContinuousMap.exists_matrix_solution_of_forall_pow t b (r : R) hr hb
  let z : P ⟶ ⨁ fun _ : Fin m ↦ P := biproduct.lift fun j ↦ (e (a j)).asHom
  have hzy : z ≫ A = y := by
    apply biproduct.hom_ext
    intro i
    have hh := happ z i
    simp only [z, biproduct.lift_π] at hh
    change (e (∑ j, t i j * e.symm (e (a j)))).asHom = _ at hh
    simp only [RingEquiv.symm_apply_apply] at hh
    rw [ha i] at hh
    simpa only [b, RingEquiv.apply_symm_apply, Category.assoc] using hh.symm
  rw [← hy, ← hzy, Category.assoc, cokernel.condition, comp_zero]

private theorem map_quotient_zero
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    {V N : C} (x : V ⟶ N) (k : ℕ)
    (hx : x ≫ cokernel.π (k • 𝟙 N) = 0) :
    F.map x ≫ cokernel.π (k • 𝟙 (F.obj N)) = 0 := by
  have hz : F.map x ≫ F.map (cokernel.π (k • 𝟙 N)) = 0 := by
    simpa only [Functor.map_comp, Functor.map_zero] using congrArg F.map hx
  let d := cokernel.desc (F.map (k • 𝟙 N)) (cokernel.π (k • 𝟙 (F.obj N))) (by
    rw [F.map_nsmul, F.map_id]
    exact cokernel.condition _)
  have hd : F.map (cokernel.π (k • 𝟙 N)) ≫
      (PreservesCokernel.iso F (k • 𝟙 N)).hom ≫ d =
      cokernel.π (k • 𝟙 (F.obj N)) := by
    rw [← Category.assoc, PreservesCokernel.π_iso_hom, cokernel.π_desc]
  rw [← hd, ← Category.assoc, ← Category.assoc, hz, zero_comp, zero_comp]

private theorem iso_quotient_zero
    {C : Type*} [Category C] [Abelian C] {V N M : C}
    (e : N ≅ M) (x : V ⟶ N) (k : ℕ)
    (hx : x ≫ cokernel.π (k • 𝟙 N) = 0) :
    (x ≫ e.hom) ≫ cokernel.π (k • 𝟙 M) = 0 := by
  let d := cokernel.desc (k • 𝟙 N) (e.hom ≫ cokernel.π (k • 𝟙 M)) (by
    calc
      (k • 𝟙 N) ≫ (e.hom ≫ cokernel.π (k • 𝟙 M)) =
          e.hom ≫ ((k • 𝟙 M) ≫ cokernel.π (k • 𝟙 M)) := by
        simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
          Category.id_comp]
      _ = 0 := by rw [cokernel.condition, comp_zero])
  have hd : cokernel.π (k • 𝟙 N) ≫ d = e.hom ≫ cokernel.π (k • 𝟙 M) :=
    cokernel.π_desc _ _ _
  rw [Category.assoc, ← hd, ← Category.assoc, hx, zero_comp]

private theorem local_sections_separated
    (ell : ℕ) [Fact ell.Prime]
    (E : IntermediateField ℚ_[ell] (PadicAlgCl ell))
    [FiniteDimensional ℚ_[ell] E]
    (D : CommRingCat.{u}) [IsWContractibleRing D]
    (N : Mod (Sheaf (ProEt.topology (Spec D)) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) (Spec D)))
    (hN : Mod.IsFinitelyPresented
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) (Spec D)) N)
    (x : Mod.regular (condensedRingObj (Profinite.padicIntegersRingObj ell E) (Spec D)) ⟶ N)
    (hx : ∀ k : ℕ, x ≫ cokernel.π (ell ^ (k + 1) • 𝟙 N) = 0) : x = 0 := by
  classical
  let := PadicAlgCl.normedFieldOfAlgebra ell E
  let O := PadicAlgCl.integers ell E
  let Y := Spec D
  let R := condensedRingObj (Profinite.padicIntegersRingObj ell E) Y
  let S := ConnectedComponents Y
  have : CompactSpace O := PadicAlgCl.compactSpace_integers ell E
  have : ExtremallyDisconnected S :=
    IsWContractibleRing.extremallyDisconnected_connectedComponents
  let c : C(Y, S) := ⟨fun y ↦ ⟦y⟧, ConnectedComponents.continuous_coe⟩
  let e₀ : C(S, O) ≃+* C(Y, O) := RingEquiv.ofBijective
    (ContinuousMap.compRightAlgHom ℤ O c).toRingHom (by
      constructor
      · intro f g h
        apply ContinuousMap.ext
        intro s
        obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe s
        exact congrArg (fun q : C(Y, O) ↦ q y) h
      · intro f
        exact ⟨⟨f.continuous.connectedComponentsLift,
          f.continuous.connectedComponentsLift_continuous⟩, rfl⟩)
  let e₁ : C(Y, O) ≃+* End (Mod.regular R) := RingEquiv.ofBijective
    (Mod.regularEndRingHom.comp (continuousMapCoefficientSectionRingHom Y O))
    (Mod.regularEndRingHom_bijective.comp
      (continuousMapCoefficientSectionRingHom_bijective Y O))
  have hW : (ProEt.topology Y).IsWeaklyContractible.{u + 1} (ProEt.mk (𝟙 Y)) :=
    ProEt.isWeaklyContractible_of_iso (R := D) (Iso.refl _)
  have : Projective (MonoidalCategory.tensorUnit
      (Sheaf (ProEt.topology Y) Ab.{u + 1})) :=
    Projective.of_iso
      (asIso (Functor.LaxMonoidal.ε (presheafToSheaf (ProEt.topology Y)
        Ab.{u + 1}))).symm
      (projective_presheafToSheaf_const (ProEt.isTerminalMkId Y) hW)
  have : Projective (Mod.regular R) := Mod.projective_regular
  obtain ⟨n, m, A, ⟨i⟩⟩ := hN
  have hxi : ∀ k : ℕ,
      (x ≫ i.hom) ≫ cokernel.π (ell ^ k • 𝟙 (cokernel A)) = 0 := by
    intro k
    cases k with
    | zero =>
        have hz : cokernel.π (ell ^ 0 • 𝟙 (cokernel A)) = 0 := by
          calc
            cokernel.π (ell ^ 0 • 𝟙 (cokernel A)) =
                𝟙 _ ≫ cokernel.π (ell ^ 0 • 𝟙 (cokernel A)) :=
              (Category.id_comp _).symm
            _ = (ell ^ 0 • 𝟙 (cokernel A)) ≫
                cokernel.π (ell ^ 0 • 𝟙 (cokernel A)) := by
              apply congrArg (fun f : cokernel A ⟶ cokernel A ↦
                f ≫ cokernel.π (ell ^ 0 • 𝟙 (cokernel A)))
              simp only [pow_zero, one_nsmul]
            _ = 0 := cokernel.condition _
        rw [hz, comp_zero]
    | succ k => exact iso_quotient_zero i x _ (hx k)
  have hz := separated_cokernel_sections (Mod.regular R) (e₀.trans e₁) ell
    (PadicAlgCl.natCast_mem_maximalIdeal_integers ell E) A (x ≫ i.hom) hxi
  exact (cancel_mono i.hom).mp (hz.trans zero_comp.symm)

private theorem unit_section_surjective (Y : Scheme.{u})
    (M : Sheaf (ProEt.topology Y) Ab.{u + 1})
    (s : M.obj.obj (Opposite.op (ProEt.mk (𝟙 Y)))) :
    ∃ f : MonoidalCategory.tensorUnit (Sheaf (ProEt.topology Y) Ab.{u + 1}) ⟶ M,
      Sheaf.unitHomEval (ProEt.mk (𝟙 Y)) f = s := by
  let J := ProEt.topology Y
  let T := ProEt.mk (𝟙 Y)
  let hT := ProEt.isTerminalMkId Y
  let adj := sheafificationAdjunction J Ab.{u + 1}
  let a : MonoidalCategory.tensorUnit (Y.ProEtᵒᵖ ⥤ Ab.{u + 1}) ⟶ M.obj :=
    { app U := AddCommGrpCat.ofHom ((zmultiplesHom _ (M.obj.map (hT.from U.unop).op s)).comp
        AddEquiv.ulift.toAddMonoidHom)
      naturality U V g := by
        simp only [Monoidal.tensorUnit_obj, Monoidal.tensorUnit_map, Opposite.op_unop,
          AddEquiv.toAddMonoidHom_eq_coe, Category.id_comp]
        ext n
        erw [AddCommGrpCat.hom_comp]
        simp only [AddCommGrpCat.hom_ofHom, AddMonoidHom.coe_comp, Function.comp_apply,
          zmultiplesHom_apply, AddMonoidHom.coe_ofClass]
        erw [map_zsmul]
        congr 1
        erw [← Functor.map_comp_apply, show (hT.from U.unop).op ≫ g =
          (hT.from V.unop).op from Quiver.Hom.unop_inj (hT.hom_ext _ _)] }
  let f := inv (Functor.OplaxMonoidal.η (presheafToSheaf J Ab.{u + 1})) ≫
    (adj.homEquiv _ _).symm a
  have he : Functor.LaxMonoidal.ε (sheafToPresheaf J Ab.{u + 1}) ≫ f.hom = a := by
    apply (adj.homEquiv _ _).symm.injective
    change (adj.homEquiv _ _).symm
      (Functor.LaxMonoidal.ε (sheafToPresheaf J Ab.{u + 1}) ≫
        (sheafToPresheaf J Ab.{u + 1}).map f) = _
    rw [Adjunction.homEquiv_naturality_right_symm]
    have he₀ : (adj.homEquiv _ _).symm
        (Functor.LaxMonoidal.ε (sheafToPresheaf J Ab.{u + 1})) =
        Functor.OplaxMonoidal.η (presheafToSheaf J Ab.{u + 1}) :=
      Equiv.symm_apply_apply _ _
    rw [he₀]
    simp only [f, IsIso.hom_inv_id_assoc]
  refine ⟨f, ?_⟩
  change (Functor.LaxMonoidal.ε (sheafToPresheaf J Ab.{u + 1}) ≫ f.hom).app
    (Opposite.op T) (ULift.up 1) = s
  rw [he]
  have hfrom : hT.from T = 𝟙 T := hT.hom_ext _ _
  change (1 : ℤ) • M.obj.map (hT.from T).op s = s
  rw [hfrom]
  change (1 : ℤ) • M.obj.map (𝟙 (Opposite.op T)) s = s
  rw [M.obj.map_id]
  change (1 : ℤ) • s = s
  exact one_zsmul _

private theorem terminal_component_zero
    (ell : ℕ) [Fact ell.Prime]
    (E : IntermediateField ℚ_[ell] (PadicAlgCl ell))
    [FiniteDimensional ℚ_[ell] E]
    (D : CommRingCat.{u}) [IsWContractibleRing D]
    (N : Mod (Sheaf (ProEt.topology (Spec D)) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) (Spec D)))
    (hN : Mod.IsFinitelyPresented
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) (Spec D)) N)
    {V : Mod (Sheaf (ProEt.topology (Spec D)) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) (Spec D))}
    (v : V ⟶ N) (hv : ∀ k : ℕ, v ≫ cokernel.π (ell ^ (k + 1) • 𝟙 N) = 0) :
    v.hom.hom.app (Opposite.op (ProEt.mk (𝟙 (Spec D)))) = 0 := by
  apply AddCommGrpCat.ext
  intro s
  obtain ⟨a, ha⟩ := unit_section_surjective (Spec D) V.X s
  have hzero : Mod.regularLift V a ≫ v = 0 := by
    apply local_sections_separated ell E D N hN
    intro k
    rw [Category.assoc, hv, comp_zero]
  have hh : a ≫ v.hom = 0 := by
    have h := congrArg (fun q :
        Mod.regular (condensedRingObj (Profinite.padicIntegersRingObj ell E) (Spec D)) ⟶ N ↦
        (CategoryTheory.MonObj.one :
          MonoidalCategory.tensorUnit (Sheaf (ProEt.topology (Spec D)) Ab.{u + 1}) ⟶
          condensedRingObj (Profinite.padicIntegersRingObj ell E) (Spec D)) ≫ q.hom) hzero
    simp only [Mod.comp_hom', Mod.zero_hom] at h
    erw [← Category.assoc, Mod.one_comp_regularLift] at h
    exact h
  have h := congrArg (fun q :
      MonoidalCategory.tensorUnit (Sheaf (ProEt.topology (Spec D)) Ab.{u + 1}) ⟶ N.X ↦
      Sheaf.unitHomEval.{u + 1, u, u + 1} (ProEt.mk (𝟙 (Spec D))) q) hh
  change v.hom.hom.app (Opposite.op (ProEt.mk (𝟙 (Spec D))))
    (Sheaf.unitHomEval.{u + 1, u, u + 1} (ProEt.mk (𝟙 (Spec D))) a) = 0 at h
  rw [ha] at h
  exact h

/-- Finite-presentation separatedness for ordinary integral quotients.

Source: Hemo--Richarz--Scholbach, Propositions 5.1 and 7.6 and Theorem 7.7;
Bhatt--Scholze, Section 6.1.
(blueprint: lem-sp-original-integral-ordinary-quotient-kernel-separated-finite-presentation).

Proof. On a w-contractible affine test, the regular module is projective.
A finite presentation and the quotient-zero hypothesis give continuous matrix
approximations on its component space. Pointwise Krull intersection and compact
projectivity give an exact continuous relation. Thus every section of the
morphism is zero on the test. Weakly etale pullback is restriction, and the
sheaf axiom detects zero on the cover by such tests. -/
theorem originalIntegralOrdinaryQuotientKernel_separated_finitePresentation
    (ell : ℕ) [Fact ell.Prime]
    (E : IntermediateField ℚ_[ell] (PadicAlgCl ell))
    [FiniteDimensional ℚ_[ell] E]
    (Y : Scheme.{u})
    (N : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) Y))
    (hN : Mod.IsFinitelyPresented
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) Y) N)
    {V : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) Y)}
    (u : V ⟶ N)
    (hu : ∀ n : ℕ, u ≫ cokernel.π (ell ^ (n + 1) • 𝟙 N) = 0) :
    u = 0 := by
  classical
  let Λ := Profinite.padicIntegersRingObj ell E
  apply Mod.hom_ext
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  change u.hom.hom.app U = 0
  obtain ⟨ι, D, hD, g, hg⟩ := Scheme.exists_isWContractibleRing_cover U.unop.left
  have (i : ι) : IsWContractibleRing (D i) := hD i
  have (i : ι) : WeaklyEtale (g i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hg ⟨i⟩
  have : MorphismProperty.IsStableUnderComposition (@WeaklyEtale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  let w (i : ι) : Spec (D i) ⟶ Y := g i ≫ U.unop.hom
  have (i : ι) : WeaklyEtale (w i) := inferInstanceAs (WeaklyEtale (g i ≫ U.unop.hom))
  let Φ (i : ι) : (Spec (D i)).ProEt ⥤ Y.ProEt :=
    MorphismProperty.Over.map ⊤ (inferInstance : @WeaklyEtale _ _ (w i))
  let W (i : ι) : Y.ProEt := (Φ i).obj (ProEt.mk (𝟙 (Spec (D i))))
  let a (i : ι) : W i ⟶ U.unop := MorphismProperty.Over.homMk (g i) (by
    change g i ≫ U.unop.hom = 𝟙 _ ≫ (g i ≫ U.unop.hom)
    exact (Category.id_comp _).symm)
  have hcov : Sieve.ofArrows W a ∈ ProEt.topology Y U.unop := by
    apply Precoverage.generate_mem_toGrothendieck
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    exact hg
  apply N.X.property.hom_ext_ofArrows a hcov
  intro i
  have hz : u.hom.hom.app (Opposite.op (W i)) = 0 := by
    let F := (w i)^*⟦Λ⟧
    have hq : ∀ k : ℕ, F.map u ≫
        cokernel.π (ell ^ (k + 1) • 𝟙 (F.obj N)) = 0 :=
      fun k ↦ map_quotient_zero F u _ (hu k)
    have ht := terminal_component_zero ell E (D i) (F.obj N)
      (IsFinitelyPresented.upperStar Λ (w i) hN) (F.map u) hq
    let e := (upperStarForgetIso Λ (w i)).symm ≪≫
      Functor.isoWhiskerLeft (Mod.forget (condensedRingObj Λ Y))
        (ProEtale.upperStarIsoLocalizationRestriction Ab.{u + 1} (w i) inferInstance)
    have hn := congrArg (fun q ↦ q.hom.app (Opposite.op (ProEt.mk (𝟙 (Spec (D i))))))
      (e.hom.naturality u)
    have hh : ((e.hom.app V).hom.app (Opposite.op (ProEt.mk (𝟙 (Spec (D i)))))) ≫
        u.hom.hom.app (Opposite.op (W i)) = 0 := by
      change (F.map u).hom.hom.app (Opposite.op (ProEt.mk (𝟙 (Spec (D i))))) ≫
        (e.hom.app N).hom.app (Opposite.op (ProEt.mk (𝟙 (Spec (D i))))) =
        (e.hom.app V).hom.app (Opposite.op (ProEt.mk (𝟙 (Spec (D i))))) ≫
        u.hom.hom.app (Opposite.op (W i)) at hn
      refine hn.symm.trans ?_
      rw [ht]
      exact zero_comp
    exact (cancel_epi ((e.hom.app V).hom.app
      (Opposite.op (ProEt.mk (𝟙 (Spec (D i))))))).mp (hh.trans comp_zero.symm)
  rw [← u.hom.hom.naturality, hz, comp_zero, zero_comp]
end AlgebraicGeometry.ProEtale.CondensedRing
