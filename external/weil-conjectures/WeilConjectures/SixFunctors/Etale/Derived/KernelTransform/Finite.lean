/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition

/-!

# Kernel transforms at finite coefficients

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_comp`: composition of kernel
  transforms, at finite coefficients.
- `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_diagonal`: the kernel transform of a
  kernel supported on the diagonal is a tensor product.

See `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform` for the implementation notes.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
  {S V : Scheme.{u}} (π : V ⟶ S)

/-- The kernel transform of a kernel `Δ_* N` supported on the diagonal, with shift `0`, is
tensoring with `N`, at a general coefficient category `A`, from the inputs of the six-functor
formalism it uses: `RΔ_* ≅ RΔ_!` (`hΔ`), the projection formula for `Δ` at `N` (`hpf`) and
`RΔ_! ⋙ Rp₂,! ≅ 𝟭` (`hcomp`), the composition law of `Rf_!` for `Δ ≫ p₂ = 𝟙`. Then
`Rp₂,!(p₁^* K ⊗ᴸ Δ_* N) ≅ Rp₂,!(RΔ_!(Δ^* p₁^* K ⊗ᴸ N)) ≅ K ⊗ᴸ N`, using a braiding of the
derived categories and `Δ ≫ p₁ = 𝟙`. -/
theorem nonempty_iso_kernelTransform_diagonal_of_nonempty_iso
    [HasCompactification (pullback.snd π π)] [HasCompactification (pullback.diagonal π)]
    (N : DerivedCategory (Sheaf V.smallEtaleTopology A))
    (hΔ : Nonempty (R((pullback.diagonal π)_*[A]) ≅ R(pullback.diagonal π)_![A]))
    (hpf : Nonempty ((derivedTensor A (pullback π π)).obj
        ((R(pullback.diagonal π)_![A]).obj N) ≅
      L((pullback.diagonal π)^*[A]) ⋙ (derivedTensor A V).obj N ⋙
        R(pullback.diagonal π)_![A]))
    (hcomp : Nonempty (R(pullback.diagonal π)_![A] ⋙ R(pullback.snd π π)_![A] ≅ 𝟭 _)) :
    Nonempty (kernelTransform A π π ((R((pullback.diagonal π)_*[A])).obj N) 0 ≅
      derivedTensorRight A V N) := by
  obtain ⟨eΔ⟩ := hΔ
  obtain ⟨eP⟩ := hpf
  obtain ⟨ec⟩ := hcomp
  obtain ⟨_⟩ := DerivedCategory.nonempty_braidedCategory (Sheaf (pullback π π).smallEtaleTopology A)
  obtain ⟨_⟩ := DerivedCategory.nonempty_braidedCategory (Sheaf V.smallEtaleTopology A)
  have hb {X : Scheme.{u}} [BraidedCategory (DerivedCategory (Sheaf X.smallEtaleTopology A))]
      (𝒦 : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
      derivedTensorRight A X 𝒦 ≅ (derivedTensor A X).obj 𝒦 :=
    NatIso.ofComponents (fun M ↦ β_ M 𝒦) fun f ↦ BraidedCategory.braiding_naturality_left f 𝒦
  let eL : D((pullback.fst π π)^*[A]) ⋙ L((pullback.diagonal π)^*[A]) ≅ 𝟭 _ :=
    Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory A _).symm _ ≪≫
      (leftDerivedUpperStarComp A (pullback.diagonal π) (pullback.fst π π) (𝟙 V)
        (by simp)).symm ≪≫
      leftDerivedUpperStarIsoMapDerivedCategory A (𝟙 V) ≪≫
      Functor.mapDerivedCategoryNatIso (Etale.upperStarId A V) ≪≫
      Functor.mapDerivedCategoryIdIso _
  let e₁ : derivedTensorRight A _ ((R((pullback.diagonal π)_*[A])).obj N) ≅
      L((pullback.diagonal π)^*[A]) ⋙ (derivedTensor A V).obj N ⋙
        R(pullback.diagonal π)_![A] :=
    (derivedTensorRightFunctor A _).mapIso (eΔ.app N) ≪≫ hb _ ≪≫ eP
  exact ⟨Functor.isoWhiskerLeft D((pullback.fst π π)^*[A])
      (Functor.isoWhiskerRight e₁ (R(pullback.snd π π)_![A] ⋙ shiftFunctor _ (0 : ℤ))) ≪≫
    (Iso.refl _ : _ ≅ (D((pullback.fst π π)^*[A]) ⋙ L((pullback.diagonal π)^*[A])) ⋙
      (derivedTensor A V).obj N ⋙ (R(pullback.diagonal π)_![A] ⋙ R(pullback.snd π π)_![A]) ⋙
        shiftFunctor _ (0 : ℤ)) ≪≫
    Functor.isoWhiskerRight eL _ ≪≫ Functor.leftUnitor _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight ec _ ≪≫ Functor.leftUnitor _ ≪≫
      shiftFunctorZero _ ℤ) ≪≫ Functor.rightUnitor _ ≪≫ (hb N).symm⟩

end General

variable (Λ : Type (u + 1)) [CommRing Λ]
variable {S V V' V'' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S) (π'' : V'' ⟶ S)

/-- The composite of the kernel transform of `𝒦` with shift `a` and the kernel transform of
`𝒦'` with shift `c` is the kernel transform of the convolution `𝒦' ∗ 𝒦` with shift `a + c`.
The composite is read on the triple product, in the cartesian square

```
    V ×ₛ V' ×ₛ V'' ──r₁₂──▶ V ×ₛ V'
          │                    │
       r₂₃│                    │p₂
          ▼                    ▼
      V' ×ₛ V'' ─────q₁─────▶ V'
```

with `r₁₃ : V ×ₛ V' ×ₛ V'' ⟶ V ×ₛ V''` the remaining projection and
`q₂ : V' ×ₛ V'' ⟶ V''` the second projection.

Class: torsion; decided by compact-support base change and the projection formula for `Rf_!`,
which need `[Finite Λ]`. The composition law of `Rf_!` is applied
to `r₁₃ ≫ s₂ = r₂₃ ≫ q₂`, `s₂ : V ×ₛ V'' ⟶ V''` being the second projection, which is why that
composite is assumed to admit a compactification.
(sketch blueprint: `proposition-fourier-inversion`; blueprint: `proposition-fourier-inversion`) -/
theorem nonempty_iso_kernelTransform_comp [Finite Λ]
    [LocallyOfFiniteType π] [QuasiCompact π] [LocallyOfFiniteType π'] [QuasiCompact π']
    [HasCompactification (pullback.tripleProj₁₃ π π' π'')]
    [HasCompactification (pullback.snd π π')] [HasCompactification (pullback.snd π' π'')]
    [HasCompactification (pullback.snd π π'')]
    [HasCompactification (pullback.tripleProj₁₃ π π' π'' ≫ pullback.snd π π'')]
    (𝒦 : DerivedCategory (Sheaf (pullback π π').smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (𝒦' : DerivedCategory (Sheaf (pullback π' π'').smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (a c : ℤ) :
    Nonempty (kernelTransform (ModuleCat.{u + 1} Λ) π π' 𝒦 a ⋙
          kernelTransform (ModuleCat.{u + 1} Λ) π' π'' 𝒦' c ≅
        kernelTransform (ModuleCat.{u + 1} Λ) π π''
          (kernelConvolution (ModuleCat.{u + 1} Λ) π π' π'' 𝒦 𝒦') (a + c)) :=
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ
    (IsPullback.of_hasPullback (pullback.snd π π') (pullback.fst π' π''))
  nonempty_iso_kernelTransform_comp_of_nonempty_iso (ModuleCat.{u + 1} Λ) π π' π''
    (fun f g _ _ _ _ ↦ nonempty_iso_rightDerivedLowerShriek_comp Λ f g)
    ⟨asIso (rightDerivedLowerShriekBaseChangeMap _
      (IsPullback.of_hasPullback (pullback.snd π π') (pullback.fst π' π'')))⟩
    (fun L ↦ nonempty_iso_rightDerivedLowerShriek_comp_derivedTensorRight _ _ L
      (fun K ↦ hasProjectionFormula_of_finite Λ _ K L))
    (fun K ↦ nonempty_iso_derivedTensor_obj_rightDerivedLowerShriek _ _ K
      (fun L ↦ hasProjectionFormula_of_finite Λ _ K L)) 𝒦 𝒦' a c

/-- The kernel transform of a kernel `Δ_* N` supported on the diagonal of `V ×_S V`, with
shift `0`, is tensoring with `N`:

`Rp₂,!(p₁^* K ⊗ᴸ Δ_* N) ≅ K ⊗ᴸ N`,

naturally in `K`, where `Δ` is the diagonal of the separated morphism `π`:

```
             Δ
        V ──────▶ V ×ₛ V ──p₂──▶ V
         ╲          │
          ╲ 𝟙       │p₁
           ╲        ▼
            ──────▶ V
```

with `Δ ≫ p₁ = 𝟙 = Δ ≫ p₂`. For `N = Λ` this says that `Δ_* Λ` is the identity kernel.

Class: torsion. The blueprint proof is formal: the projection formula for the closed immersion
`Δ`, `Δ_* = Δ_!` and `Δ ≫ p₂ = 𝟙`
(`AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_diagonal_of_nonempty_iso`). Here
`[Finite Λ]` enters through the projection formula and the composition law of `Rf_!`, and
`[IsSeparated π]` makes `Δ` a closed immersion.
(sketch blueprint: `sec-Fourier-inversion`, proof) -/
theorem nonempty_iso_kernelTransform_diagonal [Finite Λ] [IsSeparated π] [QuasiCompact π]
    [HasCompactification (pullback.snd π π)]
    (N : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty (kernelTransform (ModuleCat.{u + 1} Λ) π π
          ((R((pullback.diagonal π)_*[ModuleCat.{u + 1} Λ])).obj N) 0 ≅
        derivedTensorRight (ModuleCat.{u + 1} Λ) V N) := by
  have key : ∀ (g : V ⟶ V) [HasCompactification g], g = 𝟙 V →
      Nonempty (R(g)_![ModuleCat.{u + 1} Λ] ≅ 𝟭 _) := by
    rintro g _ rfl
    exact ⟨rightDerivedLowerShriekIsoRightDerivedLowerStar _ (𝟙 V) ≪≫
      (Etale.lowerStar (ModuleCat.{u + 1} Λ) (𝟙 V)).rightDerivedFunctorIsoMapDerivedCategory ≪≫
      Functor.mapDerivedCategoryNatIso (Etale.lowerStarId (ModuleCat.{u + 1} Λ) V) ≪≫
      Functor.mapDerivedCategoryIdIso _⟩
  have : HasCompactification (pullback.diagonal π ≫ pullback.snd π π) :=
    HasCompactification.of_eq (f := 𝟙 V) (pullback.diagonal_snd π).symm
  obtain ⟨ec⟩ := nonempty_iso_rightDerivedLowerShriek_comp Λ (pullback.diagonal π)
    (pullback.snd π π)
  obtain ⟨e₁⟩ := key _ (pullback.diagonal_snd π)
  exact nonempty_iso_kernelTransform_diagonal_of_nonempty_iso _ π N
    ⟨(rightDerivedLowerShriekIsoRightDerivedLowerStar _ _).symm⟩
    (nonempty_iso_derivedTensor_obj_rightDerivedLowerShriek _ _ N
      (fun L ↦ hasProjectionFormula_of_finite Λ _ N L)) ⟨ec.symm ≪≫ e₁⟩

end AlgebraicGeometry.Etale
