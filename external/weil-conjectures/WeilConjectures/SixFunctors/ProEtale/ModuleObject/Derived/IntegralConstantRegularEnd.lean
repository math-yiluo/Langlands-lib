/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapMulLeft
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.LocallyFree
public import WeilConjectures.NumberTheory.Padics.Extension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.IntegralRegularEnd
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit

/-!
# Multiplication by powers of a uniformizer on the integral coefficient ring

Let `E ⊆ ℚ̄_ℓ` be a finite subextension of `ℚ_ℓ` with ring of integers `𝒪_E`, and `X` a scheme.
The multiplication by `x ∈ 𝒪_E` on `𝒪_{E,X}` (`ProEtale.padicIntegersRegularEndOfAlgebra`) is
the image under `p_X^*` of the multiplication by `x` on `𝒪̲_E`
(`ProEtale.padicIntegersRegularEndOfAlgebra_hom_eq_map`). Hence it is multiplicative in `x`
(`ProEtale.padicIntegersRegularEndOfAlgebra_mul`) and a monomorphism for `x ≠ 0`
(`ProEtale.mono_padicIntegersRegularEndOfAlgebra`).

We also record that finitely presented module objects are stable under binary biproducts
(`CategoryTheory.Mod.IsFinitelyPresented.biprod`) and that an endomorphism `k ≫ h` of the unit
acts by zero on the cokernel of `h` (`CategoryTheory.comp_whiskerRight_cokernel_eq_zero`).

This file does not import
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace CategoryTheory.Mod

/-- The image of the multiplication by a global section under a lax monoidal functor. -/
lemma regularLift_regular_obj_hom {C D : Type*} [Category* C] [MonoidalCategory C] [Category* D]
    [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal] {A : C} [MonObj A] (c : 𝟙_ C ⟶ A) :
    (regularLift (regular (F.obj A)) (Functor.LaxMonoidal.ε F ≫ F.map c)).hom =
      F.map (regularLift (regular A) c).hom := by
  have hact : act (regular (F.obj A)).X = Functor.LaxMonoidal.μ F A A ≫ F.map μ[A] := rfl
  have hact' : act (regular A).X = μ[A] := rfl
  simp only [regularLift, homMk_hom, MonoidalCategory.whiskerLeft_comp, Category.assoc,
    Functor.map_comp, hact, hact', Functor.LaxMonoidal.μ_natural_right_assoc,
    Functor.LaxMonoidal.right_unitality_inv_assoc]

/-- In a commutative monoid object, multiplying by a global section on the left or on the right
agree. -/
lemma rightUnitor_inv_whiskerLeft_mul {C : Type*} [Category* C] [MonoidalCategory C]
    [BraidedCategory C] {R : C} [MonObj R] [IsCommMonObj R] (σ : 𝟙_ C ⟶ R) :
    (ρ_ R).inv ≫ R ◁ σ ≫ μ[R] = (λ_ R).inv ≫ σ ▷ R ≫ μ[R] := by
  conv_rhs => rw [← IsCommMonObj.mul_comm R]
  rw [BraidedCategory.braiding_naturality_left_assoc, leftUnitor_inv_braiding_assoc]

/-- For a commutative monoid object, the multiplication by a global section on the regular module
is its action `globalSmul`. -/
lemma regularLift_regular_hom {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]
    {R : C} [MonObj R] [IsCommMonObj R] (σ : 𝟙_ C ⟶ R) :
    (regularLift (regular R) σ).hom = globalSmul σ (regular R) :=
  rightUnitor_inv_whiskerLeft_mul σ

end CategoryTheory.Mod

namespace Profinite

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]

/-- The multiplication by the constant global section `t` on the regular module `T̲` is the
multiplication by the constant `t`. -/
lemma regularLift_continuousMapConstRingHom_hom (t : T) :
    (Mod.regularLift (Mod.regular (continuousMapRingObj.{u} T))
      (continuousMapConstRingHom T t).hom).hom =
      continuousMapRingObjMulLeft T t := by
  rw [Mod.regularLift_regular_hom]
  exact globalSmul_continuousMapConstRingHom T t

end Profinite

namespace CategoryTheory

/-- An endomorphism `k ≫ h` of the unit which factors through `h` acts by zero on the cokernel
of `h`. -/
lemma comp_whiskerRight_cokernel_eq_zero {C : Type*} [Category* C] [MonoidalCategory C]
    [Preadditive C] (k h : 𝟙_ C ⟶ 𝟙_ C) [HasCokernel h] : (k ≫ h) ▷ cokernel h = 0 := by
  have : Epi (𝟙_ C ◁ cokernel.π h) := by
    rw [id_whiskerLeft]
    infer_instance
  rw [← cancel_epi (𝟙_ C ◁ cokernel.π h), whisker_exchange, whiskerRight_id, comp_zero]
  simp only [Category.assoc]
  rw [← unitors_inv_equal, ← leftUnitor_inv_naturality, cokernel.condition_assoc]
  simp

namespace Limits

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C] [HasCokernels C]

/-- The cokernel of a direct sum of morphisms is the direct sum of the cokernels. -/
noncomputable def cokernelBiprodMapIso {A B A' B' : C} (f : A ⟶ B) (f' : A' ⟶ B') :
    cokernel (biprod.map f f') ≅ cokernel f ⊞ cokernel f' where
  hom := cokernel.desc _ (biprod.map (cokernel.π f) (cokernel.π f')) (by
    apply biprod.hom_ext' <;> simp)
  inv := biprod.desc (cokernel.desc f (biprod.inl ≫ cokernel.π _) (by
      rw [← biprod.inl_map_assoc, cokernel.condition, comp_zero]))
    (cokernel.desc f' (biprod.inr ≫ cokernel.π _) (by
      rw [← biprod.inr_map_assoc, cokernel.condition, comp_zero]))
  hom_inv_id := by
    apply coequalizer.hom_ext
    apply biprod.hom_ext' <;> simp
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply coequalizer.hom_ext <;> simp

end Limits

namespace Mod

variable {C : Type*} [Category* C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  {R : C} [MonObj R] [PreservesFiniteColimits (MonoidalCategory.tensorLeft R)]

/-- A direct sum of two finitely presented module objects is finitely presented. -/
lemma IsFinitelyPresented.biprod {M N : Mod C R} (hM : IsFinitelyPresented R M)
    (hN : IsFinitelyPresented R N) : IsFinitelyPresented R (M ⊞ N) := by
  obtain ⟨n, m, f, ⟨e⟩⟩ := hM
  obtain ⟨n', m', f', ⟨e'⟩⟩ := hN
  refine ⟨n + n', m + m', (biprodBiproductFinIso _ m m').inv ≫ biprod.map f f' ≫
    (biprodBiproductFinIso _ n n').hom, ⟨biprod.mapIso e e' ≪≫ (cokernelBiprodMapIso f f').symm ≪≫
    cokernel.mapIso _ _ (biprodBiproductFinIso _ m m') (biprodBiproductFinIso _ n n') (by simp)⟩⟩

/-- The regular module object is finitely presented. -/
lemma isFinitelyPresented_regular : IsFinitelyPresented R (regular R) :=
  IsFree.isFinitelyPresented ⟨1, ⟨(biproductUniqueIso (fun _ : Fin 1 ↦ regular R)).symm⟩⟩

/-- The cokernel of an endomorphism of the regular module object is finitely presented. -/
lemma isFinitelyPresented_cokernel_regular (f : regular R ⟶ regular R) :
    IsFinitelyPresented R (cokernel f) :=
  let e := (biproductUniqueIso (fun _ : Fin 1 ↦ regular R)).symm
  ⟨1, 1, e.inv ≫ f ≫ e.hom, ⟨cokernel.mapIso _ _ e e (by simp)⟩⟩

end Mod

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]

/-- The underlying map of the multiplication by `x ∈ 𝒪_E` on `𝒪_{E,X}` is the image under `p_X^*`
of the multiplication by `x` on `𝒪̲_E`. -/
lemma padicIntegersRegularEndOfAlgebra_hom_eq_map (x : PadicAlgCl.integers ℓ E) :
    letI := PadicAlgCl.normedFieldOfAlgebra ℓ E
    (padicIntegersRegularEndOfAlgebra X ℓ E x).hom = (upperStarFromPoint X).map
      (Profinite.continuousMapRingObjMulLeft _ x) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  rw [padicIntegersRegularEndOfAlgebra, Mod.regularLift_regular_obj_hom,
    Profinite.regularLift_continuousMapConstRingHom_hom]

/-- The multiplication by `x * y` on `𝒪_{E,X}` is the multiplication by `x` followed by the
multiplication by `y`. -/
lemma padicIntegersRegularEndOfAlgebra_mul (x y : PadicAlgCl.integers ℓ E) :
    padicIntegersRegularEndOfAlgebra X ℓ E (x * y) =
      padicIntegersRegularEndOfAlgebra X ℓ E x ≫ padicIntegersRegularEndOfAlgebra X ℓ E y := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  refine Mod.hom_ext _ _ ?_
  rw [Mod.comp_hom', padicIntegersRegularEndOfAlgebra_hom_eq_map,
    padicIntegersRegularEndOfAlgebra_hom_eq_map, padicIntegersRegularEndOfAlgebra_hom_eq_map,
    ← Functor.map_comp]
  congr 1
  ext S a
  exact ULift.ext (ContinuousMap.ext fun s ↦
    (congrArg (· * _) (mul_comm x y)).trans (mul_assoc _ _ _))

/-- The multiplication by a nonzero `x ∈ 𝒪_E` on `𝒪_{E,X}` is a monomorphism. -/
lemma mono_padicIntegersRegularEndOfAlgebra {x : PadicAlgCl.integers ℓ E} (hx : x ≠ 0) :
    Mono (padicIntegersRegularEndOfAlgebra X ℓ E x) := by
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E
  have : PreservesFiniteLimits pointUpperStar.{u} := by
    unfold pointUpperStar Functor.sheafPullbackConstruction.sheafPullback
    infer_instance
  have : PreservesFiniteLimits (upperStarFromPoint X) := by
    unfold upperStarFromPoint
    infer_instance
  let h := Profinite.continuousMapRingObjMulLeft.{u} _ x
  have hm : Mono h := by
    refine (sheafToPresheaf _ _).mono_of_mono_map ?_
    have (S : Profinite.{u}ᵒᵖ) : Mono (((sheafToPresheaf _ _).map h).app S) := by
      rw [AddCommGrpCat.mono_iff_injective]
      intro a b hab
      exact ULift.ext (ContinuousMap.ext fun s ↦ mul_left_cancel₀ hx
        (congrArg (fun z : ULift.{u + 1} C(S.unop, PadicAlgCl.integers ℓ E) ↦ z.down s) hab))
    exact NatTrans.mono_of_mono_app _
  refine (Mod.forget _).mono_of_mono_map ?_
  rw [Mod.forget_map, padicIntegersRegularEndOfAlgebra_hom_eq_map]
  infer_instance

end AlgebraicGeometry.ProEtale
