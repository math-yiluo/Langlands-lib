/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import WeilConjectures.CategoryTheory.IntegralProjectivePresentationComplete
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Tactic.FunProp
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedProjective
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ContinuousMapCoefficientSections
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Scalars
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FinitelyPresentedStalk
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.WeaklyEtaleBaseChange
import WeilConjectures.AlgebraicGeometry.ProEtale.WContractibleDisjointCover
import WeilConjectures.NumberTheory.Padics.IntegersAlgebra
import WeilConjectures.CategoryTheory.ModuleObjects.RegularEndBijective
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OriginalIntegralOrdinaryQuotientKernelSeparatedFinitePresentation

/-! # Section convergence on a finite-presentation integral chart

This is the scalar section-existence step of integral compatible morphism gluing.
It constructs no morphism and supplies no restriction or linearity data.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.InternalAbelianSheafModule
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry Scheme

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

private theorem iso_quotient_eq
    {C : Type*} [Category C] [Abelian C] {V N M : C}
    (e : N ≅ M) (x y : V ⟶ N) (k : ℕ)
    (h : x ≫ cokernel.π (k • 𝟙 N) = y ≫ cokernel.π (k • 𝟙 N)) :
    (x ≫ e.hom) ≫ cokernel.π (k • 𝟙 M) =
      (y ≫ e.hom) ≫ cokernel.π (k • 𝟙 M) := by
  have hz : (x - y) ≫ cokernel.π (k • 𝟙 N) = 0 := by
    rw [Preadditive.sub_comp, h, sub_self]
  have hh := iso_quotient_zero e (x - y) k hz
  simpa only [Preadditive.sub_comp, sub_eq_zero] using hh

private theorem fp_limit
    {C : Type*} [Category C] [Abelian C] [HasFiniteBiproducts C]
    (P : C) [Projective P]
    {S : Type*} {R : Type} [TopologicalSpace S] [CompactSpace S] [T2Space S]
    [ExtremallyDisconnected S] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [CompactSpace R] [T2Space R]
    (e : C(S, R) ≃+* End P) (r : ℕ)
    {n m : ℕ} (A : (⨁ fun _ : Fin m ↦ P) ⟶ ⨁ fun _ : Fin n ↦ P)
    {N : C} (i : N ≅ cokernel A) (b : ℕ → (P ⟶ N))
    (hb : ∀ k l : ℕ, k ≤ l →
      b l ≫ cokernel.π (r ^ (k + 1) • 𝟙 N) =
        b k ≫ cokernel.π (r ^ (k + 1) • 𝟙 N)) :
    ∃ z : P ⟶ N, ∀ k : ℕ,
      z ≫ cokernel.π (r ^ (k + 1) • 𝟙 N) =
        b k ≫ cokernel.π (r ^ (k + 1) • 𝟙 N) := by
  obtain ⟨z, hz⟩ := exists_cokernel_limit_of_continuous_end P e r A
    (fun k ↦ b k ≫ i.hom) (fun k l hkl ↦ iso_quotient_eq i _ _ _ (hb k l hkl))
  refine ⟨z ≫ i.inv, fun k ↦ ?_⟩
  have hh := iso_quotient_eq i.symm z (b k ≫ i.hom) _ (hz k)
  simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using hh

private theorem quotient_comparison
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F] (N : C) (k : ℕ) :
    ∃ c : F.obj (cokernel (k • 𝟙 N)) ≅ cokernel (k • 𝟙 (F.obj N)),
      F.map (cokernel.π (k • 𝟙 N)) ≫ c.hom =
        cokernel.π (k • 𝟙 (F.obj N)) := by
  let e : cokernel (F.map (k • 𝟙 N)) ≅ cokernel (k • 𝟙 (F.obj N)) :=
    cokernelIsoOfEq (by rw [F.map_nsmul, F.map_id])
  refine ⟨PreservesCokernel.iso F (k • 𝟙 N) ≪≫ e, ?_⟩
  rw [Iso.trans_hom, ← Category.assoc, PreservesCokernel.π_iso_hom]
  exact π_comp_cokernelIsoOfEq_hom _

private theorem section_limit_transport
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteColimits F]
    (G : C ⥤ Ab.{u + 1}) (H : D ⥤ Ab.{u + 1})
    (e : F ⋙ H ≅ G) (N : C) (r : ℕ)
    (hl : ∀ b : ℕ → H.obj (F.obj N),
      (∀ k l : ℕ, k ≤ l →
        H.map (cokernel.π (r ^ (k + 1) • 𝟙 (F.obj N))) (b l) =
          H.map (cokernel.π (r ^ (k + 1) • 𝟙 (F.obj N))) (b k)) →
      ∃ x : H.obj (F.obj N), ∀ k : ℕ,
        H.map (cokernel.π (r ^ (k + 1) • 𝟙 (F.obj N))) x =
          H.map (cokernel.π (r ^ (k + 1) • 𝟙 (F.obj N))) (b k))
    (b : ℕ → G.obj N)
    (hb : ∀ k l : ℕ, k ≤ l →
      G.map (cokernel.π (r ^ (k + 1) • 𝟙 N)) (b l) =
        G.map (cokernel.π (r ^ (k + 1) • 𝟙 N)) (b k)) :
    ∃ x : G.obj N, ∀ k : ℕ,
      G.map (cokernel.π (r ^ (k + 1) • 𝟙 N)) x =
        G.map (cokernel.π (r ^ (k + 1) • 𝟙 N)) (b k) := by
  classical
  let a (k : ℕ) : H.obj (F.obj N) := (e.app N).inv (b k)
  have ha (k : ℕ) : (e.app N).hom (a k) = b k := by
    change ((e.app N).inv ≫ (e.app N).hom) (b k) = b k
    rw [Iso.inv_hom_id]
    rfl
  have nat (k : ℕ) (x : H.obj (F.obj N)) :
      (e.app (cokernel (r ^ (k + 1) • 𝟙 N))).hom
        (H.map (F.map (cokernel.π (r ^ (k + 1) • 𝟙 N))) x) =
      G.map (cokernel.π (r ^ (k + 1) • 𝟙 N)) ((e.app N).hom x) :=
    ConcreteCategory.congr_hom (e.hom.naturality _) x
  choose c hc using fun k ↦ quotient_comparison F N (r ^ (k + 1))
  have hc' (k : ℕ) (x : H.obj (F.obj N)) :
      H.map (c k).hom (H.map (F.map (cokernel.π (r ^ (k + 1) • 𝟙 N))) x) =
        H.map (cokernel.π (r ^ (k + 1) • 𝟙 (F.obj N))) x := by
    have hh := congrArg H.map (hc k)
    rw [Functor.map_comp] at hh
    exact ConcreteCategory.congr_hom hh x
  have hab (k l : ℕ) (hkl : k ≤ l) :
      H.map (cokernel.π (r ^ (k + 1) • 𝟙 (F.obj N))) (a l) =
        H.map (cokernel.π (r ^ (k + 1) • 𝟙 (F.obj N))) (a k) := by
    rw [← hc', ← hc']
    congr 1
    apply (AddCommGrpCat.mono_iff_injective
      (e.app (cokernel (r ^ (k + 1) • 𝟙 N))).hom).mp inferInstance
    rw [nat, nat, ha, ha]
    exact hb k l hkl
  obtain ⟨x, hx⟩ := hl a hab
  refine ⟨(e.app N).hom x, fun k ↦ ?_⟩
  rw [← ha k, ← nat, ← nat]
  congr 1
  apply (AddCommGrpCat.mono_iff_injective (H.map (c k).hom)).mp inferInstance
  rw [hc', hc']
  exact hx k

private theorem section_limit_of_cover
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    (N : Sheaf J Ab.{u + 1}) (Q : ℕ → Sheaf J Ab.{u + 1}) (q : ∀ n, N ⟶ Q n)
    (hsep : ∀ (V : Cᵒᵖ) (x y : N.obj.obj V),
      (∀ n, (q n).hom.app V x = (q n).hom.app V y) → x = y)
    (U : Cᵒᵖ) {ι : Type*} (W : ι → C) (a : ∀ i, W i ⟶ U.unop)
    (hcov : Sieve.ofArrows W a ∈ J U.unop) (b : ℕ → N.obj.obj U)
    (x : ∀ i, N.obj.obj (Opposite.op (W i)))
    (hx : ∀ i n, (q n).hom.app (Opposite.op (W i)) (x i) =
      (q n).hom.app (Opposite.op (W i)) (N.obj.map (a i).op (b n))) :
    ∃ z : N.obj.obj U, ∀ n, (q n).hom.app U z = (q n).hom.app U (b n) := by
  have hmatch : Presieve.Arrows.Compatible (N.obj ⋙ forget Ab.{u + 1}) a x := by
    intro i j V f g hfg
    apply hsep (Opposite.op V)
    intro n
    change (q n).hom.app (Opposite.op V) (N.obj.map f.op (x i)) =
      (q n).hom.app (Opposite.op V) (N.obj.map g.op (x j))
    rw [NatTrans.naturality_apply (q n).hom f.op,
      NatTrans.naturality_apply (q n).hom g.op, hx i n, hx j n,
      NatTrans.naturality_apply (q n).hom (a i).op,
      NatTrans.naturality_apply (q n).hom (a j).op]
    simp only [← Functor.map_comp_apply, ← CategoryTheory.op_comp, hfg]
  have hs : Presieve.IsSheaf J (N.obj ⋙ forget Ab.{u + 1}) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (Presheaf.isSheaf_comp_of_isSheaf J N.obj (forget Ab.{u + 1}) N.property)
  obtain ⟨z, hz, _⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp
    ((Presieve.isSheafFor_iff_generate _).mpr (hs _ hcov)) x hmatch
  change ∀ i, N.obj.map (a i).op z = x i at hz
  refine ⟨z, fun n ↦ ?_⟩
  have hQ : Presieve.IsSheaf J ((Q n).obj ⋙ forget Ab.{u + 1}) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      (Presheaf.isSheaf_comp_of_isSheaf J (Q n).obj (forget Ab.{u + 1}) (Q n).property)
  apply ((Presieve.isSheafFor_iff_generate _).mpr (hQ _ hcov)).isSeparatedFor.ext
  rintro V f ⟨i⟩
  change (Q n).obj.map (a i).op ((q n).hom.app U z) =
    (Q n).obj.map (a i).op ((q n).hom.app U (b n))
  rw [← NatTrans.naturality_apply (q n).hom (a i).op,
    ← NatTrans.naturality_apply (q n).hom (a i).op, hz]
  exact hx i n

private theorem sections_separated
    (ell : ℕ) [Fact ell.Prime]
    (E : IntermediateField ℚ_[ell] (PadicAlgCl ell))
    [FiniteDimensional ℚ_[ell] E]
    (Y : Scheme.{u})
    (N : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) Y))
    (hN : Mod.IsFinitelyPresented
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) Y) N)
    (U : Y.ProEtᵒᵖ) (x y : N.X.obj.obj U)
    (hxy : ∀ n, (cokernel.π (ell ^ (n + 1) • 𝟙 N)).hom.hom.app U x =
      (cokernel.π (ell ^ (n + 1) • 𝟙 N)).hom.hom.app U y) : x = y := by
  let Q := fun n : ℕ ↦ cokernel (ell ^ (n + 1) • 𝟙 N)
  let A : N ⟶ ∏ᶜ Q := Pi.lift fun n ↦ cokernel.π (ell ^ (n + 1) • 𝟙 N)
  have hA : Mono A := Preadditive.mono_of_cancel_zero A (fun g hg ↦
    originalIntegralOrdinaryQuotientKernel_separated_finitePresentation ell E Y N hN g
      (fun n ↦ by
        have hh := congrArg (fun f ↦ f ≫ Pi.π Q n) hg
        simpa only [A, Category.assoc, Pi.lift_comp_π, zero_comp] using hh))
  let T := Mod.forget (condensedRingObj (Profinite.padicIntegersRingObj ell E) Y) ⋙
    sheafToPresheaf (ProEt.topology Y) Ab.{u + 1} ⋙
      (evaluation Y.ProEtᵒᵖ Ab.{u + 1}).obj U ⋙ forget Ab.{u + 1}
  have hmono : Mono (T.map A) := inferInstance
  apply (CategoryTheory.mono_iff_injective (T.map A)).mp hmono
  apply (Types.isLimitEquivSections
    (isLimitOfPreserves T (limit.isLimit (Discrete.functor Q)))).injective
  apply Subtype.ext
  funext n
  change T.map (Pi.π Q n.as) (T.map A x) = T.map (Pi.π Q n.as) (T.map A y)
  have hp : A ≫ Pi.π Q n.as = cokernel.π (ell ^ (n.as + 1) • 𝟙 N) := Pi.lift_comp_π _ _
  have hh := congrArg T.map hp
  rw [Functor.map_comp] at hh
  exact (ConcreteCategory.congr_hom hh x).trans
    ((hxy n.as).trans (ConcreteCategory.congr_hom hh y).symm)

private theorem local_limit
    (ell : ℕ) [Fact ell.Prime]
    (E : IntermediateField ℚ_[ell] (PadicAlgCl ell))
    [FiniteDimensional ℚ_[ell] E]
    (D : CommRingCat.{u}) [IsWContractibleRing D]
    (N : Mod (Sheaf (ProEt.topology (Spec D)) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) (Spec D)))
    (hN : Mod.IsFinitelyPresented
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) (Spec D)) N)
    (b : ℕ → N.X.obj.obj (Opposite.op (ProEt.mk (𝟙 (Spec D)))))
    (hb : ∀ n m : ℕ, n ≤ m →
      ((cokernel.π (ell ^ (n + 1) • 𝟙 N)).hom.hom.app
        (Opposite.op (ProEt.mk (𝟙 (Spec D))))) (b m) =
        ((cokernel.π (ell ^ (n + 1) • 𝟙 N)).hom.hom.app
          (Opposite.op (ProEt.mk (𝟙 (Spec D))))) (b n)) :
    ∃ x : N.X.obj.obj (Opposite.op (ProEt.mk (𝟙 (Spec D)))), ∀ n : ℕ,
      ((cokernel.π (ell ^ (n + 1) • 𝟙 N)).hom.hom.app
        (Opposite.op (ProEt.mk (𝟙 (Spec D))))) x =
        ((cokernel.π (ell ^ (n + 1) • 𝟙 N)).hom.hom.app
          (Opposite.op (ProEt.mk (𝟙 (Spec D))))) (b n) := by
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
  let T := ProEt.mk (𝟙 Y)
  let ev (M : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1}) R) :=
    Sheaf.unitHomEvalAddEquiv (ProEt.isTerminalMkId Y) M.X
  let a (k : ℕ) : Mod.regular R ⟶ N := Mod.regularLift N ((ev N).symm (b k))
  have ha (k : ℕ) : Sheaf.unitHomEval.{u + 1, u, u + 1} T
      ((MonObj.one : MonoidalCategory.tensorUnit _ ⟶ R) ≫ (a k).hom) = b k := by
    rw [Mod.one_comp_regularLift]
    exact (ev N).apply_symm_apply (b k)
  have hab (k l : ℕ) (hkl : k ≤ l) :
      a l ≫ cokernel.π (ell ^ (k + 1) • 𝟙 N) =
        a k ≫ cokernel.π (ell ^ (k + 1) • 𝟙 N) := by
    apply Mod.regular_hom_ext
    apply Sheaf.unitHomEval_injective.{u + 1, u, u + 1} (ProEt.isTerminalMkId Y)
    change (cokernel.π (ell ^ (k + 1) • 𝟙 N)).hom.hom.app (Opposite.op T)
        (Sheaf.unitHomEval.{u + 1, u, u + 1} T
          ((MonObj.one : MonoidalCategory.tensorUnit _ ⟶ R) ≫ (a l).hom)) =
      (cokernel.π (ell ^ (k + 1) • 𝟙 N)).hom.hom.app (Opposite.op T)
        (Sheaf.unitHomEval.{u + 1, u, u + 1} T
          ((MonObj.one : MonoidalCategory.tensorUnit _ ⟶ R) ≫ (a k).hom))
    rw [ha, ha]
    exact hb k l hkl
  obtain ⟨n, m, A, ⟨i⟩⟩ := hN
  obtain ⟨z, hz⟩ := fp_limit (Mod.regular R) (e₀.trans e₁) ell A i a hab
  refine ⟨Sheaf.unitHomEval.{u + 1, u, u + 1} T
    ((MonObj.one : MonoidalCategory.tensorUnit _ ⟶ R) ≫ z.hom), fun k ↦ ?_⟩
  have hh := congrArg (fun f : Mod.regular R ⟶ cokernel (ell ^ (k + 1) • 𝟙 N) ↦
    Sheaf.unitHomEval.{u + 1, u, u + 1} T
      ((MonObj.one : MonoidalCategory.tensorUnit _ ⟶ R) ≫ f.hom))
    (hz k)
  simpa only [Mod.comp_hom', ← Category.assoc, Sheaf.unitHomEval_comp, ha] using hh

/-- Convergence of individual sections of a finitely presented integral module.
Source: Hemo--Richarz--Scholbach, Proposition 5.1; Bhatt--Scholze, Section 6.1.
(blueprint: lem-sp-original-integral-ordinary-quotient-compatible-limit-finite-presentation).
Proof: cover the test U by w-contractible affine pro-etale tests. Weakly etale
pullback is restriction and preserves the finite presentation. The regular
coefficient module on each such test is projective, and its endomorphism ring is
the ring of continuous O_E-valued functions on the compact extremally disconnected
component space. Present N as a cokernel of a matrix between finite sums of this
regular module. Identify each section with a morphism from the regular module;
the supplied ordinary quotient equations give compatible regular-module maps.
Apply exists_cokernel_limit_of_continuous_end to this finite presentation. Its
compact matrix argument constructs the regular-module map with every prescribed
reduction. Transport it back through the presentation isomorphism and evaluate
at the unit section to obtain a local section limit. Finite-presentation
quotient-separatedness proves uniqueness. Restrict to overlaps, refine them by
w-contractible tests and use this uniqueness to identify the restrictions.
The sheaf condition now glues the local limits on U, with all reductions checked
on the cover. Empty tests, zero presentations and bounded torsion are included. -/
theorem originalIntegralOrdinaryQuotient_compatibleLimit_finitePresentation
    (ell : ℕ) [Fact ell.Prime]
    (E : IntermediateField ℚ_[ell] (PadicAlgCl ell))
    [FiniteDimensional ℚ_[ell] E]
    (Y : Scheme.{u})
    (N : Mod (Sheaf (ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) Y))
    (hN : Mod.IsFinitelyPresented
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) Y) N) :
    let F := sectionModuleFunctor (ProEt.topology Y)
      (condensedRingObj (Profinite.padicIntegersRingObj ell E) Y)
    ∀ (U : Y.ProEtᵒᵖ) (b : ℕ → (F.obj N).val.obj U),
      (∀ n m : ℕ, n ≤ m →
        ((F.map (cokernel.π (ell ^ (n + 1) • 𝟙 N))).val.app U) (b m) =
          ((F.map (cokernel.π (ell ^ (n + 1) • 𝟙 N))).val.app U) (b n)) →
      ∃ x : (F.obj N).val.obj U, ∀ n : ℕ,
        ((F.map (cokernel.π (ell ^ (n + 1) • 𝟙 N))).val.app U) x =
          ((F.map (cokernel.π (ell ^ (n + 1) • 𝟙 N))).val.app U) (b n) := by
  classical
  change ∀ (U : Y.ProEtᵒᵖ) (b : ℕ → N.X.obj.obj U),
    (∀ n m : ℕ, n ≤ m →
      (cokernel.π (ell ^ (n + 1) • 𝟙 N)).hom.hom.app U (b m) =
        (cokernel.π (ell ^ (n + 1) • 𝟙 N)).hom.hom.app U (b n)) →
    ∃ x : N.X.obj.obj U, ∀ n : ℕ,
      (cokernel.π (ell ^ (n + 1) • 𝟙 N)).hom.hom.app U x =
        (cokernel.π (ell ^ (n + 1) • 𝟙 N)).hom.hom.app U (b n)
  intro U b hb
  let Λ := Profinite.padicIntegersRingObj ell E
  obtain ⟨ι, D, hD, g, hg⟩ := Scheme.exists_isWContractibleRing_cover U.unop.left
  have (i : ι) : IsWContractibleRing (D i) := hD i
  have hg' (i : ι) : WeaklyEtale (g i) :=
    Scheme.proetalePrecoverage_le_precoverage_weaklyEtale _ hg ⟨i⟩
  let w (i : ι) : Spec (D i) ⟶ Y := g i ≫ U.unop.hom
  have (i : ι) : WeaklyEtale (w i) :=
    MorphismProperty.comp_mem @WeaklyEtale (g i) U.unop.hom (hg' i) U.unop.prop
  let W (i : ι) : Y.ProEt :=
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale (w i))).obj
      (ProEt.mk (𝟙 (Spec (D i))))
  let a (i : ι) : W i ⟶ U.unop := MorphismProperty.Over.homMk (g i) (by
    change g i ≫ U.unop.hom = 𝟙 _ ≫ (g i ≫ U.unop.hom)
    exact (Category.id_comp _).symm)
  have hcov : Sieve.ofArrows W a ∈ ProEt.topology Y U.unop := by
    apply Precoverage.generate_mem_toGrothendieck
    rw [ProEt.mem_precoverage_iff, Presieve.map_ofArrows]
    exact hg
  have hlocal (i : ι) : ∃ x : N.X.obj.obj (Opposite.op (W i)), ∀ n : ℕ,
      (cokernel.π (ell ^ (n + 1) • 𝟙 N)).hom.hom.app (Opposite.op (W i)) x =
      (cokernel.π (ell ^ (n + 1) • 𝟙 N)).hom.hom.app (Opposite.op (W i))
        (N.X.obj.map (a i).op (b n)) := by
    let F := (w i)^*⟦Λ⟧
    let T := ProEt.mk (𝟙 (Spec (D i)))
    let H := Mod.forget (condensedRingObj Λ (Spec (D i))) ⋙
      sheafToPresheaf (ProEt.topology (Spec (D i))) Ab.{u + 1} ⋙
        (evaluation (Spec (D i)).ProEtᵒᵖ Ab.{u + 1}).obj (Opposite.op T)
    let G := Mod.forget (condensedRingObj Λ Y) ⋙
      sheafToPresheaf (ProEt.topology Y) Ab.{u + 1} ⋙
        (evaluation Y.ProEtᵒᵖ Ab.{u + 1}).obj (Opposite.op (W i))
    let e := (upperStarForgetIso Λ (w i)).symm ≪≫
      Functor.isoWhiskerLeft (Mod.forget (condensedRingObj Λ Y))
        (ProEtale.upperStarIsoLocalizationRestriction Ab.{u + 1} (w i) inferInstance)
    let ee : F ⋙ H ≅ G := Functor.isoWhiskerRight e
      (sheafToPresheaf (ProEt.topology (Spec (D i))) Ab.{u + 1} ⋙
        (evaluation (Spec (D i)).ProEtᵒᵖ Ab.{u + 1}).obj (Opposite.op T))
    apply section_limit_transport F G H ee N ell
      (local_limit ell E (D i) (F.obj N) (IsFinitelyPresented.upperStar Λ (w i) hN))
      (fun k ↦ N.X.obj.map (a i).op (b k))
    intro n m hnm
    change (cokernel.π (ell ^ (n + 1) • 𝟙 N)).hom.hom.app (Opposite.op (W i))
        (N.X.obj.map (a i).op (b m)) =
      (cokernel.π (ell ^ (n + 1) • 𝟙 N)).hom.hom.app (Opposite.op (W i))
        (N.X.obj.map (a i).op (b n))
    let q := (cokernel.π (ell ^ (n + 1) • 𝟙 N)).hom.hom
    rw [NatTrans.naturality_apply q (a i).op, NatTrans.naturality_apply q (a i).op,
      hb n m hnm]
  choose x hx using hlocal
  exact section_limit_of_cover N.X (fun n ↦ (cokernel (ell ^ (n + 1) • 𝟙 N)).X)
    (fun n ↦ (cokernel.π (ell ^ (n + 1) • 𝟙 N)).hom)
    (sections_separated ell E Y N hN) U W a hcov b x hx

end AlgebraicGeometry.ProEtale.CondensedRing
