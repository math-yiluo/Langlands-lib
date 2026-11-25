/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.TraceFormulaCoefficientSetup
public import WeilConjectures.SixFunctors.Supporting.SixFunctorOperationDatumStages
public import WeilConjectures.TraceFormula.TraceFormulaFiniteDerivedOperations
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientTensorCtf
import WeilConjectures.CategoryTheory.Ringed.Tensor.RingedTensorComparisonExtension
import all WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated

/-! # Tensor closure of the finite geometric domain

Source: latest blueprint proposition-six-operations-dctf (ii), proposition-six-operations-dctf--14.
(blueprint: lem-trf-finite-geometric-tensor-domain).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem sfStabilityTorOfIso
    (X : Scheme.{u}) (A : Type u) [CommRing A]
    {K L : proEtaleDerivedCategory X A} (e : K ≅ L) (a b : ℤ)
    (ht : HasProEtaleTorAmplitude X A K a b) : HasProEtaleTorAmplitude X A L a b := by
  refine ⟨ht.1, ?_⟩
  intro M P hM f hf hP N i hi
  exact ht.2 M P (hM.map (fun j ↦ j ≪≫ e.symm)) f hf hP N i hi

private theorem sfStabilityFiniteTorOfIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ)
    (X : Scheme.{u})
    {K L : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1))}
    (e : K ≅ L) (hK : finiteTorConstructible l E (n + 1) (by omega) X K) :
    finiteTorConstructible l E (n + 1) (by omega) X L := by
  let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  have : ObjectProperty.IsClosedUnderIsomorphisms
      (intrinsicFiniteTorsionConstructible l E (n + 1) (by omega) X) :=
    (proEtale_bounded_constructible_isTriangulated X
      (Padic.coefficientExtensionRing l E (n + 1))).1
  refine ⟨ObjectProperty.prop_of_iso _ e hK.1, ?_⟩
  obtain ⟨a, b, ht⟩ := hK.2
  refine ⟨a, b, ht.1, ?_⟩
  intro M P hM f hf hP N i hi
  exact ht.2 M P (hM.map (fun j ↦ j ≪≫ e.symm)) f hf hP N i hi

/-- The recorded finite intrinsic tensor preserves the geometric finite-Tor domain.
Source: latest blueprint proposition-six-operations-dctf (ii) and
proposition-six-operations-dctf--14 (blueprint: lem-trf-finite-geometric-tensor-domain).

Proof: take ordinary cochain representatives and a K-flat resolution of the first.
The signed tensor comparison identifies the tensor on these representatives with the
specified intrinsic tensor. The two finite Tor intervals give their sum interval,
and finite-coefficient tensor constructibility gives bounded constructibility.
Transport these properties along the comparison. Empty schemes, zero objects and
level one require no additional hypothesis. -/
theorem finiteGeometricTensor_domain
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ)
    (X : SixFunctorSpace D)
    (K L : proEtaleDerivedCategory X.obj.left (Padic.coefficientExtensionRing l E (n + 1)))
    (hK : finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X.obj.left K)
    (hL : finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X.obj.left L) :
    finiteTorConstructible l E (n + 1) (Nat.succ_pos n) X.obj.left
      ((traceFormulaFiniteTensor l E X.obj.left n).obj (K, L)) := by
  let : X.obj.left.Over (Spec (.of D.k)) := ⟨X.obj.hom⟩
  have : LocallyOfFiniteType (X.obj.left ↘ Spec (.of D.k)) := X.property.1
  have : QuasiCompact (X.obj.left ↘ Spec (.of D.k)) := X.property.2
  classical
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let R := proEtaleConstantRing X.obj.left A
  let C := proEtaleRingModules X.obj.left R
  let : HasDerivedCategory C := HasDerivedCategory.standard C
  let Kc := (DerivedCategory.Q (C := C)).objPreimage K
  let Lc := (DerivedCategory.Q (C := C)).objPreimage L
  let eK := (DerivedCategory.Q (C := C)).objObjPreimageIso K
  let eL := (DerivedCategory.Q (C := C)).objObjPreimageIso L
  have hKc := sfStabilityFiniteTorOfIso l E n X.obj.left eK.symm hK
  have hLc := sfStabilityFiniteTorOfIso l E n X.obj.left eL.symm hL
  obtain ⟨P, g, hP, _, hg, _⟩ := CochainComplex.exists_isKFlatResolutionGeneral Kc
  obtain ⟨t, _, _⟩ := ringedTensorComparison_extension.{u + 1, u, u, u + 2}
    (ProEt.topology X.obj.left) R
    (traceFormulaFiniteClosed l E X.obj.left n)
    (traceFormulaFiniteTensorModels.{u} l E X.obj.left n)
  have : IsIso (DerivedCategory.Q.map g) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso C g).2 hg
  let e : derivedTensor X.obj.left A Kc Lc P g hg hP ≅
      (traceFormulaFiniteTensor l E X.obj.left n).obj (K, L) :=
    t P Lc (.inl hP) ≪≫
      (traceFormulaFiniteTensor l E X.obj.left n).mapIso
        (Iso.prod (C := proEtaleDerivedCategory X.obj.left A)
          (D := proEtaleDerivedCategory X.obj.left A)
          (asIso (DerivedCategory.Q.map g) ≪≫ eK) eL)
  have ht (a b c d : ℤ) (htK : HasProEtaleTorAmplitude X.obj.left A K a b)
      (htL : HasProEtaleTorAmplitude X.obj.left A L c d) :=
    (finiteCoefficient_tensor_ctf D l hl E (n + 1) (by omega) X.obj.left
      Kc Lc P g hg hP a b hKc
      (sfStabilityTorOfIso X.obj.left A eK.symm a b htK) hLc.1).2 c d hLc
      (sfStabilityTorOfIso X.obj.left A eL.symm c d htL)
  obtain ⟨a, b, htK⟩ := hK.2
  obtain ⟨c, d, htL⟩ := hL.2
  exact sfStabilityFiniteTorOfIso l E n X.obj.left e (ht a b c d htK htL).1

end WeilConjectures
