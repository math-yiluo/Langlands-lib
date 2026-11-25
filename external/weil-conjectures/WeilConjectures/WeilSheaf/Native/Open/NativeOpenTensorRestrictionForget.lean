/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorComparisonData
import WeilConjectures.WeilSheaf.Native.NativeTwoSidedKFlatRepresentatives
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorRestrictionForgetKFlat

/-! # Forgetting the restriction tensor square

Source: Stacks 0E8I, 0GL1 and 015F.
(blueprint: lem-sf-native-open-tensor-restriction-forget).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison
universe u a b
open CategoryTheory CategoryTheory.Limits Opposite
private theorem natTrans_eq_of_models
    {C D E : Type*} [Category C] [Category D] [Category E]
    (Q : C ⥤ D) (P : C → Prop)
    (hmodels : ∀ M : D, ∃ K : C, P K ∧ Nonempty (Q.obj K ≅ M))
    {F G : D × D ⥤ E} (α β : F ⟶ G)
    (h : ∀ K L : C, P K → P L → α.app (Q.obj K, Q.obj L) =
      β.app (Q.obj K, Q.obj L)) : α = β := by
  apply NatTrans.ext
  funext M
  obtain ⟨K, hK, ⟨eK⟩⟩ := hmodels M.1
  obtain ⟨L, hL, ⟨eL⟩⟩ := hmodels M.2
  let e : (Q.obj K, Q.obj L) ≅ M := eK.prod eL
  apply (cancel_epi (F.map e.hom)).1
  rw [α.naturality, β.naturality, h K L hK hL]

namespace AlgebraicGeometry.ProEtaleWeilSheaf
variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]

/-- The ordinary restriction comparison agrees with the supplied native one.

Source: Stacks 0GL1 (sites-cohomology.tex, lemma-j-shriek-and-tensor), native
open tensor proof step 8, and Stacks 015F.

Proof: The balanced restriction comparison on ordinary sheaves sends both
tensor generators to their restrictions. It is invertible since the coefficient
map on the geometric open is the localized coefficient isomorphism. Apply it on
every total-complex summand. Exact restriction preserves K-flat complexes, so
localization gives an ordinary natural restriction/tensor isomorphism for the
fixed ordinary tensor models of nativeDerivedClosedComparison. On forgotten
equivariant representatives, s.restriction_forget identifies the sheaf map with
this balanced map. The presentation's restriction_summands fixes each total
summand, and restriction_model descends the equality using its specified models.
Forgetting preserves flat-term K-flat representatives by the Frobenius resolution
theorem. The fixed tensor comparisons and exact-functor compositors identify the
two localization factorizations. The two-variable localization universal property
extends equality to all derived inputs. This asserts only the restriction square.
(blueprint: lem-sf-native-open-tensor-restriction-forget). -/
theorem native_open_tensor_restriction_forget (s : NativeOpenTensorData k₀ l j)
    (rho : nativeDerivedTensor k₀ l Z ⋙ nativeOpenPull k₀ l j ≅
      (nativeOpenPull k₀ l j).prod (nativeOpenPull k₀ l j) ⋙ nativeDerivedTensor k₀ l U)
    (c : OpenTensorPresentation (ProEtaleWeilSheaf k₀ l U) (ProEtaleWeilSheaf k₀ l Z))
    (_hc :
      HEq c.R (upperStar k₀ l j) ∧
      HEq c.SA (nativeOpenSheafTensor k₀ l U) ∧ HEq c.SB (nativeOpenSheafTensor k₀ l Z) ∧
      HEq c.TA (nativeTensorTotal k₀ l U) ∧ HEq c.TB (nativeTensorTotal k₀ l Z) ∧
      HEq c.DA (nativeDerivedTensor k₀ l U) ∧ HEq c.DB (nativeDerivedTensor k₀ l Z) ∧
      HEq c.flatA (NativeIsKFlat k₀ l U) ∧ HEq c.flatB (NativeIsKFlat k₀ l Z) ∧
      HEq c.modelA (nativeOpenTensorModel k₀ l U) ∧ HEq c.modelB (nativeOpenTensorModel k₀ l Z) ∧
      HEq c.iA (nativeOpenTensorInsertion k₀ l U) ∧ HEq c.iB (nativeOpenTensorInsertion k₀ l Z) ∧
      HEq c.sheafRestriction s.sheafRestriction ∧ HEq c.restriction rho) :
    ∃ rho' :
      (nativeDerivedClosedComparison k₀ l Z).ordinaryClosed.tensor ⋙
          (ProEtale.adicUpperStar l
            (Scheme.Hom.geometricFiberMap j (comp_over j _))).mapDerivedCategory ≅
        ((ProEtale.adicUpperStar l
          (Scheme.Hom.geometricFiberMap j (comp_over j _))).mapDerivedCategory).prod
          ((ProEtale.adicUpperStar l
            (Scheme.Hom.geometricFiberMap j (comp_over j _))).mapDerivedCategory) ⋙
              (nativeDerivedClosedComparison k₀ l U).ordinaryClosed.tensor,
      ∀ M N,
        (nativeForget k₀ l U).map (rho.hom.app (M, N)) ≫
          (nativeDerivedClosedComparison k₀ l U).tensorComparison.hom.app
            ((nativeOpenPull k₀ l j).obj M, (nativeOpenPull k₀ l j).obj N) ≫
          (nativeDerivedClosedComparison k₀ l U).ordinaryClosed.tensor.map
            (Prod.mkHom ((nativeOpenForgetPull k₀ l j).hom.app M)
              ((nativeOpenForgetPull k₀ l j).hom.app N)) =
        (nativeOpenForgetPull k₀ l j).hom.app ((nativeDerivedTensor k₀ l Z).obj (M, N)) ≫
          (ProEtale.adicUpperStar l
            (Scheme.Hom.geometricFiberMap j (comp_over j _))).mapDerivedCategory.map
              ((nativeDerivedClosedComparison k₀ l Z).tensorComparison.hom.app (M, N)) ≫
          rho'.hom.app ((nativeForget k₀ l Z).obj M, (nativeForget k₀ l Z).obj N) := by
  obtain ⟨⟨dU⟩, ⟨dZ⟩⟩ :=
    native_ordinary_tensor_identifications k₀ l (U := U) (Z := Z)
  let rho' := nativeOrdinaryRestrictionTensor k₀ l j dU dZ
  let R' := (ProEtale.adicUpperStar l
    (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))))).mapDerivedCategory
  let left :=
    Functor.isoWhiskerRight rho (nativeForget k₀ l U) ≪≫
      Functor.isoWhiskerLeft ((nativeOpenPull k₀ l j).prod (nativeOpenPull k₀ l j))
        (nativeDerivedClosedComparison k₀ l U).tensorComparison ≪≫
      Functor.isoWhiskerRight
        (NatIso.prod (nativeOpenForgetPull k₀ l j) (nativeOpenForgetPull k₀ l j))
        (nativeDerivedClosedComparison k₀ l U).ordinaryClosed.tensor
  let right :=
    Functor.isoWhiskerLeft (nativeDerivedTensor k₀ l Z) (nativeOpenForgetPull k₀ l j) ≪≫
      Functor.isoWhiskerRight (nativeDerivedClosedComparison k₀ l Z).tensorComparison R' ≪≫
      Functor.isoWhiskerLeft ((nativeForget k₀ l Z).prod (nativeForget k₀ l Z)) rho'
  have hrep (P T : CochainComplex (ProEtaleWeilSheaf k₀ l Z) ℤ)
      (hP : NativeIsKFlat k₀ l Z P) (hT : NativeIsKFlat k₀ l Z T) :
      left.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) =
        right.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) := by
    simpa only [left, right, rho', R', Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, NatIso.prod_hom, Functor.prod_obj,
      Functor.comp_obj, NatTrans.prod] using
      native_open_tensor_restriction_forget_kflat k₀ l j s rho c _hc dU dZ P T hP hT
  have heq : left.hom = right.hom :=
    natTrans_eq_of_models DerivedCategory.Q (NativeIsKFlat k₀ l Z)
      (native_two_sided_kflat_representatives k₀ l Z) left.hom right.hom hrep
  refine ⟨rho', fun M N ↦ ?_⟩
  simpa only [left, right, rho', R', Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatIso.prod_hom, Functor.prod_obj,
    Functor.comp_obj, NatTrans.prod] using NatTrans.congr_app heq (M, N)

end AlgebraicGeometry.ProEtaleWeilSheaf
