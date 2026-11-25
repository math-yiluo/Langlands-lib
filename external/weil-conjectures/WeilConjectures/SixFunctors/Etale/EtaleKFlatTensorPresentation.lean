/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.SixFunctors.Etale.EtaleFiniteCoefficientHomArrow
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
/-! # Étale localization tensor on K-flat representatives
Source: Stacks 07A4 (blueprint: lem-sf-etale-kflat-tensor-presentation).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u a b v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local irreducible] finiteHomEtaleTensorModel
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
/-- Representative presentation for an abstract localization and tensor comparison.
Source: Stacks 07A4 (blueprint: lem-sf-etale-kflat-tensor-presentation). -/
def FiniteHomSourceTensorPresentationAux
    {K : Type a} {D : Type b} [Category.{v} K] [Category.{w} D]
    (q : K ⥤ D) (t : K × K ⥤ K) (T : D × D ⥤ D) (P : ObjectProperty K)
    {V : K → K → Type w} (η : ∀ x y, V x y) : Prop :=
  ∃ r : (P.ι.prod P.ι) ⋙ t ⋙ q ≅ ((P.ι ⋙ q).prod (P.ι ⋙ q)) ⋙ T,
    ∀ x y hx hy, HEq (r.inv.app (⟨x, hx⟩, ⟨y, hy⟩)) (η x y)

section Generic
variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [hD : HasDerivedCategory.{w} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [BraidedCategory C] [MonoidalClosed C]
  [Abelian.HasFunctorialFlatResolution C]
private local instance : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C

omit hD [Abelian.HasFunctorialFlatResolution C] in
private theorem native_tensorHom_eq
    {P Q P' Q' : CochainComplex C ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    f ⊗ₘ g = HomologicalComplex.tensorHom f g := by rfl

private def nativeTensorModel (X Y : CochainComplex C ℤ) :
    (tensor (DerivedCategory C)).obj (DerivedCategory.Q.obj X, DerivedCategory.Q.obj Y) ⟶
      DerivedCategory.Q.obj (HomologicalComplex.tensorObj X Y) :=
  Functor.LaxMonoidal.μ DerivedCategory.Q X Y

private theorem iso_mu (X Y : CochainComplex C ℤ)
    (hY : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat Y) :
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q X Y) := by
  have := DerivedMonoidal.isIso_counit_app_app_of_kFlat_right DerivedCategory.Qh
    (HomotopyCategory.quasiIso C (.up ℤ))
    ((HomotopyCategory.quotient C (.up ℤ)).obj X)
    ((HomotopyCategory.quotient C (.up ℤ)).obj Y)
    ((HomotopyCategory.kFlat_quotient_obj_iff _).2 hY)
  have h : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Qh
      ((HomotopyCategory.quotient C (.up ℤ)).obj X)
      ((HomotopyCategory.quotient C (.up ℤ)).obj Y)) := this
  change IsIso ((_ ⊗ₘ _) ≫ (Functor.LaxMonoidal.μ DerivedCategory.Qh _ _ ≫
    DerivedCategory.Qh.map _) ≫ _)
  infer_instance

private theorem reps_iso (P : ObjectProperty (CochainComplex C ℤ))
    (hP : ∀ Y, P Y → (HomologicalComplex.quasiIso C (.up ℤ)).kFlat Y) :
    ∃ r : (P.ι.prod P.ι) ⋙ finiteHomCochainTensorGeneral C ⋙ DerivedCategory.Q ≅
        ((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q)) ⋙ tensor _,
      ∀ X Y hx hy, r.inv.app (⟨X, hx⟩, ⟨Y, hy⟩) =
        nativeTensorModel X Y := by
  let μ : ((P.ι ⋙ DerivedCategory.Q).prod (P.ι ⋙ DerivedCategory.Q)) ⋙ tensor _ ⟶
      (P.ι.prod P.ι) ⋙ finiteHomCochainTensorGeneral C ⋙ DerivedCategory.Q :=
    { app := fun XY ↦ nativeTensorModel XY.1.obj XY.2.obj
      naturality := by
        intro XY XY' f
        simpa only [nativeTensorModel, finiteHomCochainTensorGeneral,
          Functor.comp_map, Functor.prod_map, ObjectProperty.ι_map, tensor_map,
          Prod.mkHom, native_tensorHom_eq] using
          Functor.LaxMonoidal.μ_natural DerivedCategory.Q f.1.hom f.2.hom }
  have : IsIso μ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro XY
    exact iso_mu XY.1.obj XY.2.obj (hP _ XY.2.property)
  exact ⟨(asIso μ).symm, fun _ _ _ _ ↦ rfl⟩

private theorem shared_tensor_eq :
    finiteHomDerivedTensorGeneral C = tensor (DerivedCategory C) := by rfl

private theorem reps_iso_shared (P : ObjectProperty (CochainComplex C ℤ))
    (hP : ∀ Y, P Y → (HomologicalComplex.quasiIso C (.up ℤ)).kFlat Y) :
    FiniteHomSourceTensorPresentationAux DerivedCategory.Q
      (finiteHomCochainTensorGeneral C) (finiteHomDerivedTensorGeneral C) P
      (finiteHomLocalizationTensorModelGeneral C) := by
  obtain ⟨r, hr⟩ := reps_iso P hP
  exact ⟨r, fun x y hx hy ↦ heq_of_eq (hr x y hx hy)⟩

end Generic

private theorem etale_reps_iso
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u})
    (P : ObjectProperty (CochainComplex (Sheaf W.smallEtaleTopology A) ℤ))
    (hP : ∀ Y, P Y → (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Y) :
    FiniteHomSourceTensorPresentationAux DerivedCategory.Q
      (finiteHomCochainTensorGeneral _) (finiteHomEtaleDerivedTensorGeneral A W) P
      (finiteHomEtaleLocalizationTensorModelGeneral A W) := by
  dsimp only [finiteHomEtaleDerivedTensorGeneral,
    finiteHomEtaleLocalizationTensorModelGeneral]
  exact (reps_iso_shared (C := Sheaf W.smallEtaleTopology A)
      (hD := inferInstanceAs
        (HasDerivedCategory.{u + 1} (Sheaf W.smallEtaleTopology A))) P hP)

private theorem transport_reps_iso
    {K : Type a} {D : Type b} [Category.{v} K] [Category.{w} D] (q : K ⥤ D) (t : K × K ⥤ K)
    (S T : D × D ⥤ D) (e : S = T) (P : ObjectProperty K)
    {V : K → K → Type w} (η : ∀ x y, V x y)
    (μ : ∀ x y, T.obj (q.obj x, q.obj y) ⟶ q.obj (t.obj (x, y)))
    (hη : ∀ x y, HEq (η x y) (μ x y))
    (h : FiniteHomSourceTensorPresentationAux q t T P μ) :
    FiniteHomSourceTensorPresentationAux q t S P η := by
  subst T
  obtain ⟨r, hr⟩ := h
  exact ⟨r, fun x y hx hy ↦ (hr x y hx hy).trans (hη x y).symm⟩

private theorem closedGeneral_monoidal
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) :
    (finiteHomEtaleClosedGeneral A W).monoidal =
      (inferInstance : MonoidalCategory (DerivedCategory (Sheaf W.smallEtaleTopology A))) :=
  (finiteHomEtaleClosed_existsUnique A W).choose_spec.1.1

attribute [local irreducible] finiteHomEtaleData Etale.derivedHom finiteHomEtaleClosedGeneral
  finiteHomEtaleClosedWitness finiteHomEtaleClosedWitnessRing finiteHomEtaleClosedRing

private theorem closed_normalization
    {D : Type a} [Category.{b} D] (H : Dᵒᵖ × D ⥤ D)
    (S T : CoefficientClosedStructure H) (M : MonoidalCategory D)
    (h : HEq S T) (hT : T.monoidal = M) : S.monoidal = M := by
  have e : S = T := eq_of_heq h
  exact (congrArg CoefficientClosedStructure.monoidal e).trans hT

private theorem family_monoidal
    {C : ℕ → Type a} [∀ n, Category.{b} (C n)]
    {H : ∀ n, (C n)ᵒᵖ × C n ⥤ C n}
    {F : ∀ {n m}, m ≤ n → C n ⥤ C m}
    (S : FiniteHomQuotientClosedData C H F)
    (v : ∀ n, CoefficientClosedStructure (H n))
    (M : ∀ n, MonoidalCategory (C n))
    (h : FiniteHomClosedFamilyNormalizationAux S v)
    (hv : ∀ n, (v n).monoidal = M n) : ∀ n, (S.closed n).monoidal = M n := by
  intro n
  exact closed_normalization (H n) (S.closed n) (v n) (M n) (h n) (hv n)

private theorem data_normalization :
    FiniteHomEtaleDataNormalization l E X (finiteHomEtaleData l E X) := by
  unfold finiteHomEtaleData
  exact (finiteHomEtaleData_existsUnique l E X).choose_spec.1

private theorem family_monoidal_eq
    {C : ℕ → Type a} [∀ n, Category.{b} (C n)]
    {H : ∀ n, (C n)ᵒᵖ × C n ⥤ C n}
    {F : ∀ {n m}, m ≤ n → C n ⥤ C m}
    (S : FiniteHomQuotientClosedData C H F)
    (v : ∀ n, CoefficientClosedStructure (H n))
    (h : FiniteHomClosedFamilyNormalizationAux S v) :
    ∀ n, (S.closed n).monoidal = (v n).monoidal :=
  family_monoidal S v (fun n ↦ (v n).monoidal) h (fun _ ↦ rfl)

private theorem etaleClosed_monoidal_eq (n : ℕ) :
    (finiteHomEtaleClosed l E X n).monoidal =
      (finiteHomEtaleClosedWitness l E X n).monoidal := by
  unfold finiteHomEtaleClosed
  exact family_monoidal_eq (finiteHomEtaleData l E X)
    (finiteHomEtaleClosedWitness l E X) (data_normalization l E X).closed n

private theorem closed_tensor_eq
    {D : Type a} [Category.{b} D] (H : Dᵒᵖ × D ⥤ D)
    (S : CoefficientClosedStructure H) (M : MonoidalCategory D)
    (h : S.monoidal = M) : S.tensor = @tensor D _ M := by
  cases h
  rfl

private theorem closedGeneral_tensor
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (W : Scheme.{u}) :
    (finiteHomEtaleClosedGeneral A W).tensor = finiteHomEtaleDerivedTensorGeneral A W :=
by
  unfold finiteHomEtaleDerivedTensorGeneral
  exact (closed_tensor_eq _ _ _ (closedGeneral_monoidal A W)).trans
    (shared_tensor_eq (C := Sheaf W.smallEtaleTopology A)).symm

private theorem closedWitness_tensor (n : ℕ) :
    (finiteHomEtaleClosedWitness l E X n).tensor =
      finiteHomEtaleDerivedTensorGeneral (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X := by
  unfold finiteHomEtaleClosedWitness finiteHomEtaleClosedWitnessRing finiteHomEtaleClosedRing
  exact closedGeneral_tensor _ X

private theorem closed_tensor_congr
    {D : Type a} [Category.{b} D] (H : Dᵒᵖ × D ⥤ D)
    (S T : CoefficientClosedStructure H) (h : S.monoidal = T.monoidal) :
    S.tensor = T.tensor := congrArg (fun M : MonoidalCategory D ↦ @tensor D _ M) h

/-- Localization identifies total tensor with derived tensor on a subcategory of K-flat complexes.
Source: Stacks, Cohomology on Sites, Tag 07A4
(blueprint: lem-sf-etale-kflat-tensor-presentation).

Proof: The canonical lax tensorator of the homotopy localization is invertible when
its right argument is K-flat: tensoring with that argument preserves acyclic complexes,
so this argument computes the left derived tensor. Compose with the strong monoidal
homotopy quotient to get the same assertion for cochain localization. Naturality of
the lax tensorator gives a natural transformation on the full subcategory P × P.
All its components are invertible by the K-flat hypothesis, so invert it to obtain r.
The chosen etale closed structure has the native monoidal structure, by its defining
normalization. The chosen representative map equals the localization tensorator by
FiniteHomEtaleRepresentativeNormalization.model; transport r along these equalities.
The inverse component equation follows directly. The argument includes zero complexes
and the empty subcategory, since natural isomorphisms are formed componentwise. -/
theorem finiteHomEtaleKFlatTensorPresentation (n : ℕ)
    (P : ObjectProperty (CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1))))) ℤ))
    (hP : ∀ Y, P Y → (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Y) :
    FiniteHomSourceTensorPresentationAux (finiteHomEtaleQ l E X n)
      (finiteHomCochainTensorGeneral _) (finiteHomEtaleClosed l E X n).tensor P
      (finiteHomEtaleTensorModel l E X n) := by
  have ht := (closed_tensor_congr _ _ _ (etaleClosed_monoidal_eq l E X n)).trans
    (closedWitness_tensor l E X n)
  have hη : ∀ Y Z, HEq (finiteHomEtaleTensorModel l E X n Y Z)
      (finiteHomEtaleLocalizationTensorModelGeneral (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X Y Z) := by
    intro Y Z
    unfold finiteHomEtaleTensorModel finiteHomEtaleRepresentativeData
    exact (finiteHomEtaleRepresentativeData_existsUnique l E X).choose_spec.1.model n Y Z
  exact transport_reps_iso (finiteHomEtaleQ l E X n) (finiteHomCochainTensorGeneral _)
    (finiteHomEtaleClosed l E X n).tensor _ ht P
    (finiteHomEtaleTensorModel l E X n)
    (finiteHomEtaleLocalizationTensorModelGeneral (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X) hη
    (etale_reps_iso (ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))) X P hP)

end WeilConjectures
