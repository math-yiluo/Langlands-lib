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
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Defs

/-!

# Composition of kernel transforms at a general coefficient category

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_kernelTransform_comp_of_nonempty_iso`:
  composition of kernel transforms at a general coefficient category, given the composition
  law of `Rf_!`, compact-support base change and the projection formula.

See `WeilConjectures.SixFunctors.Etale.Derived.KernelTransform` for the implementation notes.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

section Composition

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] [Etale.UpperStarPreservesFlat A]
  {FC : A → A → Type*} {CC : A → Type (u + 1)}
  [∀ (P Q : A), FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u + 1} A FC]
  [(CategoryTheory.forget A).ReflectsIsomorphisms]
  [PreservesFilteredColimitsOfSize.{u + 1, u + 1} (CategoryTheory.forget A)]
  [∀ Z : Scheme.{u}, Z.smallEtaleTopology.HasSheafCompose (CategoryTheory.forget A)]
variable {S V V' V'' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S) (π'' : V'' ⟶ S)

/-- Composition of kernel transforms, at a general coefficient category `A`, from the inputs of
the six-functor formalism it uses: the composition law of `Rf_!` (`hcomp`, which holds for
torsion coefficients, `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_comp`),
compact-support
base change (`hbc`) along the cartesian square

```
    V ×ₛ V' ×ₛ V'' ──r₁₂──▶ V ×ₛ V'
          │                    │
       r₂₃│                    │p₂
          ▼                    ▼
      V' ×ₛ V'' ─────q₁─────▶ V'
```

and the projection formula for `r₂₃` and `r₁₃` (`hpf₂₃`, `hpf₁₃`). Then the composite of the
kernel transform of `𝒦` with shift `a` and the kernel transform of `𝒦'` with shift `c` is the
kernel transform of the convolution `𝒦' ∗ 𝒦` with shift `a + c`.

Base change gives `q₁^* Rp₂,! ≅ Rr₂₃,! r₁₂^*`, the projection formula for `r₂₃` moves
`r₂₃^* 𝒦'` inside, and the composition law turns the composite into
`R(r₁₃ ≫ s₂)_!(r₁^* K ⊗ᴸ r₁₂^* 𝒦 ⊗ᴸ r₂₃^* 𝒦')`, with `r₁ = r₁₂ ≫ p₁ = r₁₃ ≫ s₁` and `s₁`,
`s₂` the projections of `V ×ₛ V''`. The projection formula for `r₁₃`, the symmetry of `⊗ᴸ`
(`AlgebraicGeometry.Etale.nonempty_iso_derivedTensor_flip`) and the composition law turn the
kernel transform of `𝒦' ∗ 𝒦` into the same expression.
(sketch blueprint: `proposition-fourier-inversion`; blueprint: `proposition-fourier-inversion`) -/
theorem nonempty_iso_kernelTransform_comp_of_nonempty_iso
    [HasCompactification (pullback.tripleProj₁₃ π π' π'')]
    [HasCompactification (pullback.snd π π')] [HasCompactification (pullback.snd π' π'')]
    [HasCompactification (pullback.snd π π'')]
    [HasCompactification (pullback.tripleProj₁₃ π π' π'' ≫ pullback.snd π π'')]
    [QuasiCompact (pullback.snd (pullback.snd π π') (pullback.fst π' π'') ≫ pullback.snd π' π'')]
    (hcomp : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [HasCompactification f]
      [HasCompactification g] [HasCompactification (f ≫ g)] [QuasiCompact (f ≫ g)],
      Nonempty (R(f ≫ g)_![A] ≅ R(f)_![A] ⋙ R(g)_![A]))
    (hbc : Nonempty (R(pullback.snd π π')_![A] ⋙ L((pullback.fst π' π'')^*[A]) ≅
      L((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A]) ⋙
        R(pullback.snd (pullback.snd π π') (pullback.fst π' π''))_![A]))
    (hpf₂₃ : ∀ L, Nonempty
      (R(pullback.snd (pullback.snd π π') (pullback.fst π' π''))_![A] ⋙
          derivedTensorRight A _ L ≅
        derivedTensorRight A _
            ((L((pullback.snd (pullback.snd π π') (pullback.fst π' π''))^*[A])).obj L) ⋙
          R(pullback.snd (pullback.snd π π') (pullback.fst π' π''))_![A]))
    (hpf₁₃ : ∀ K, Nonempty
      ((derivedTensor A _).obj ((R(pullback.tripleProj₁₃ π π' π'')_![A]).obj K) ≅
        L((pullback.tripleProj₁₃ π π' π'')^*[A]) ⋙ (derivedTensor A _).obj K ⋙
          R(pullback.tripleProj₁₃ π π' π'')_![A]))
    (𝒦 : DerivedCategory (Sheaf (pullback π π').smallEtaleTopology A))
    (𝒦' : DerivedCategory (Sheaf (pullback π' π'').smallEtaleTopology A))
    (a c : ℤ) :
    Nonempty (kernelTransform A π π' 𝒦 a ⋙ kernelTransform A π' π'' 𝒦' c ≅
        kernelTransform A π π'' (kernelConvolution A π π' π'' 𝒦 𝒦') (a + c)) := by
  -- the derived pullbacks `Lf^*` and `D(f^*)` agree
  let ι {X Y : Scheme.{u}} (f : X ⟶ Y) := leftDerivedUpperStarIsoMapDerivedCategory A f
  -- tensoring with isomorphic complexes
  let τ {X : Scheme.{u}} {N N' : DerivedCategory (Sheaf X.smallEtaleTopology A)} (e : N ≅ N') :
      derivedTensorRight A X N ≅ derivedTensorRight A X N' :=
    (derivedTensor A X).flip.mapIso e
  have hcongr {X Y : Scheme.{u}} {f g : X ⟶ Y} [HasCompactification f]
      [HasCompactification g] (h : f = g) : Nonempty (R(f)_![A] ≅ R(g)_![A]) := by
    subst h
    exact ⟨Iso.refl _⟩
  have hc : pullback.tripleProj₁₃ π π' π'' ≫ pullback.snd π π'' =
      pullback.snd (pullback.snd π π') (pullback.fst π' π'') ≫ pullback.snd π' π'' :=
    pullback.tripleProj₁₃_snd _ _ _
  have : HasCompactification
      (pullback.snd (pullback.snd π π') (pullback.fst π' π'') ≫ pullback.snd π' π'') :=
    .of_eq hc
  have : QuasiCompact (pullback.tripleProj₁₃ π π' π'' ≫ pullback.snd π π'') := hc ▸ inferInstance
  -- the inputs from the six-functor formalism
  obtain ⟨β₁₃⟩ := nonempty_iso_derivedTensor_flip A (pullback π π'')
  obtain ⟨βP⟩ := nonempty_iso_derivedTensor_flip A
    (pullback (pullback.snd π π') (pullback.fst π' π''))
  obtain ⟨c₂₃⟩ := hcomp
    (pullback.snd (pullback.snd π π') (pullback.fst π' π'')) (pullback.snd π' π'')
  obtain ⟨c₁₃⟩ := hcomp (pullback.tripleProj₁₃ π π' π'') (pullback.snd π π'')
  obtain ⟨cc⟩ := hcongr hc
  obtain ⟨pf₂₃⟩ := hpf₂₃ 𝒦'
  obtain ⟨bc₀⟩ := hbc
  obtain ⟨pf₁₃⟩ := hpf₁₃
    ((derivedTensorRight A _ ((D((pullback.snd (pullback.snd π π')
      (pullback.fst π' π''))^*[A])).obj 𝒦')).obj
      ((D((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A])).obj 𝒦))
  -- compact-support base change `q₁^* Rp₂,! ≅ Rr₂₃,! r₁₂^*`
  let bc : R(pullback.snd π π')_![A] ⋙ D((pullback.fst π' π'')^*[A]) ≅
      D((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A]) ⋙
        R(pullback.snd (pullback.snd π π') (pullback.fst π' π''))_![A] :=
    Functor.isoWhiskerLeft _ (ι _).symm ≪≫ bc₀ ≪≫ Functor.isoWhiskerRight (ι _) _
  -- `r₁₂^*` is monoidal
  let tp : derivedTensorRight A _ 𝒦 ⋙
        D((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A]) ≅
      D((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A]) ⋙
        derivedTensorRight A _
          ((D((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A])).obj 𝒦) :=
    Functor.isoWhiskerLeft _ (ι _).symm ≪≫
      derivedTensorRightCompLeftDerivedUpperStarIso A
        (pullback.fst (pullback.snd π π') (pullback.fst π' π'')) 𝒦 ≪≫
      Functor.isoWhiskerRight (ι (pullback.fst (pullback.snd π π') (pullback.fst π' π'')))
        (derivedTensorRight A _
          ((L((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A])).obj 𝒦)) ≪≫
      Functor.isoWhiskerLeft _ (τ ((ι _).app 𝒦))
  -- the projection formula for `r₂₃`
  let pf : R(pullback.snd (pullback.snd π π') (pullback.fst π' π''))_![A] ⋙
        derivedTensorRight A _ 𝒦' ≅
      derivedTensorRight A _
          ((D((pullback.snd (pullback.snd π π') (pullback.fst π' π''))^*[A])).obj 𝒦') ⋙
        R(pullback.snd (pullback.snd π π') (pullback.fst π' π''))_![A] :=
    pf₂₃ ≪≫ Functor.isoWhiskerRight (τ ((ι _).app 𝒦')) _
  -- `r₁₂ ≫ p₁ = r₁₃ ≫ s₁`
  let pc : D((pullback.fst π π')^*[A]) ⋙
        D((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A]) ≅
      D((pullback.fst π π'')^*[A]) ⋙ D((pullback.tripleProj₁₃ π π' π'')^*[A]) :=
    (Functor.isoWhiskerRight (ι _) _ ≪≫ Functor.isoWhiskerLeft _ (ι _)).symm ≪≫
      (leftDerivedUpperStarComp A _ _).symm ≪≫
      leftDerivedUpperStarComp A (pullback.tripleProj₁₃ π π' π'') (pullback.fst π π'') _
        (pullback.tripleProj₁₃_fst _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ι _) _ ≪≫ Functor.isoWhiskerLeft _ (ι _)
  -- the composite of the unshifted transforms
  let e : (D((pullback.fst π π')^*[A]) ⋙ derivedTensorRight A _ 𝒦 ⋙
        R(pullback.snd π π')_![A]) ⋙
      (D((pullback.fst π' π'')^*[A]) ⋙ derivedTensorRight A _ 𝒦' ⋙
        R(pullback.snd π' π'')_![A]) ≅
      D((pullback.fst π π'')^*[A]) ⋙
        derivedTensorRight A _ (kernelConvolution A π π' π'' 𝒦 𝒦') ⋙
        R(pullback.snd π π'')_![A] :=
    Functor.isoWhiskerLeft (D((pullback.fst π π')^*[A]) ⋙ derivedTensorRight A _ 𝒦)
        (Functor.isoWhiskerRight bc (derivedTensorRight A _ 𝒦' ⋙
          R(pullback.snd π' π'')_![A])) ≪≫
      Functor.isoWhiskerLeft D((pullback.fst π π')^*[A])
        (Functor.isoWhiskerRight tp
          (R(pullback.snd (pullback.snd π π') (pullback.fst π' π''))_![A] ⋙
            derivedTensorRight A _ 𝒦' ⋙ R(pullback.snd π' π'')_![A])) ≪≫
      Functor.isoWhiskerLeft (D((pullback.fst π π')^*[A]) ⋙
          D((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A]) ⋙
          derivedTensorRight A _
            ((D((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A])).obj 𝒦))
        (Functor.isoWhiskerRight pf R(pullback.snd π' π'')_![A]) ≪≫
      Functor.isoWhiskerLeft (D((pullback.fst π π')^*[A]) ⋙
          D((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A]) ⋙
          derivedTensorRight A _
            ((D((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A])).obj 𝒦) ⋙
          derivedTensorRight A _
            ((D((pullback.snd (pullback.snd π π') (pullback.fst π' π''))^*[A])).obj 𝒦'))
        (c₂₃.symm ≪≫ cc.symm) ≪≫
      Functor.isoWhiskerLeft (D((pullback.fst π π')^*[A]) ⋙
          D((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A]))
        (Functor.isoWhiskerRight (tensorRightTensor _ _).symm
          R(pullback.tripleProj₁₃ π π' π'' ≫ pullback.snd π π'')_![A]) ≪≫
      Functor.isoWhiskerRight pc _ ≪≫
      Functor.isoWhiskerLeft D((pullback.fst π π'')^*[A])
        (Functor.isoWhiskerRight (ι _).symm _ ≪≫
          Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight (βP.app _).symm _ ≪≫
            Functor.isoWhiskerLeft _ c₁₃) ≪≫
          Functor.isoWhiskerRight pf₁₃.symm R(pullback.snd π π'')_![A] ≪≫
          Functor.isoWhiskerRight (β₁₃.app _) R(pullback.snd π π'')_![A])
  -- moving the shifts to the end
  have : (derivedTensorRight A _ 𝒦').CommShift ℤ := commShiftDerivedTensorFlipObj A 𝒦'
  exact ⟨Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (D((pullback.fst π π')^*[A]) ⋙ derivedTensorRight A _ 𝒦 ⋙
        R(pullback.snd π π')_![A])
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight ((D((pullback.fst π' π'')^*[A]) ⋙ derivedTensorRight A _ 𝒦' ⋙
          R(pullback.snd π' π'')_![A]).commShiftIso a) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (shiftFunctorAdd _ a c).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e _⟩

end Composition

end AlgebraicGeometry.Etale
