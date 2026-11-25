/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueTensorPullPresentation
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResiduePullbackPreservesFlat
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueTensorRouteModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueScalarRouteModel

/-! # Ordinary pullback data and the derived residue tensor square

Source: Bhatt--Scholze, Lemma 6.5.9(3) and Remark 6.8.15.
(blueprint: new-integral-residue-tensor-geometry)
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance instEssentiallySmallProfinite_integralResidueTensorGeometry
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

private def rightTensorComparison {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.OplaxMonoidal] (B : C) :
    tensorRight B ⋙ F ⟶ F ⋙ tensorRight (F.obj B) where
  app M := Functor.OplaxMonoidal.δ F M B
  naturality _ _ g := (Functor.OplaxMonoidal.δ_natural_left F g B).symm

namespace AlgebraicGeometry.ProEtale.CondensedRing

-- Match the named tensor model without expanding the derived functor construction.
attribute [local irreducible] Functor.leftDerivedFunctor Functor.mapDerivedCategory

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- Ordinary pullback has a strong monoidal structure preserving flat modules,
and its derived tensor comparison agrees with the canonical scalar pull square.
The monoidal structure and both tensor presentations have already been constructed.

Source: Bhatt--Scholze, Lemma 6.5.9(3), Remark 6.8.15, balanced tensor associativity.
(blueprint: new-integral-residue-tensor-geometry)

Proof. On ordinary module objects, apply inverse image to the two balanced action
maps defining relative tensor. Inverse image preserves their coequalizer and its
ambient tensor comparison is invertible. The coefficient-pullback isomorphism
identifies the base rings, giving the ordinary tensor comparison. Its unit map is
the coefficient-pullback isomorphism on regular modules. Precompose the unit and
associativity diagrams with the tensor presentation epimorphisms: both sides are
the corresponding unit or associativity equation in the ambient inverse image.
This is the proved residueExchangeOrdinaryPullMonoidal. Inverse image preserves
flat modules: flatness is local and
is preserved by scalar extension, and the coefficient change here is an
isomorphism. This gives hFlat. The derived strong monoidal structure is the
already constructed residueExchangePullMonoidal, computed on flat resolutions.
The coefficient-pullback comparison identifies the pullback of the restricted
regular residue module in degree zero with the corresponding module on X.
Compose that coefficient isomorphism with residueExchangeTensorIso on X to give
tX. On flat resolutions the asserted square is the balanced tensor associativity
square: both routes multiply the same scalar factors. The comparison
residueExchangePullHom is the inverse mate of restriction/pullback, so its scalar
counit identity identifies it with this scalar multiplication comparison. The
canonical tensor presentation uses exactly the extension counit followed by the
balanced tensor isomorphism, hence the square is the stated one, with no freedom
to replace that presentation by an arbitrary automorphism. Uniqueness of left
derived comparisons descends the equality to every complex M. The argument does
not require flatness of the residue coefficient over the integral coefficient,
and applies also to the zero complex and the empty scheme. -/
theorem integralResidue_tensorGeometry {X Y : Scheme.{u}} (f : X ⟶ Y) :
    ∃ hFlat : (f)^*⟦integralCoeff ℓ E⟧.PreservesFlat,
        letI := residueExchangePullMonoidal ℓ E f
          (residueExchangeOrdinaryPullMonoidal ℓ E f) hFlat
          ∀ M : residueExchangeDerived (integralCoeff ℓ E) Y,
            (residueExchangeUpperStar (integralCoeff ℓ E) f).map
                ((residueExchangeTensorIso ℓ E Y).hom.app M) ≫
              Functor.OplaxMonoidal.δ (residueExchangeUpperStar (integralCoeff ℓ E) f)
                M (residueExchangeCoefficient ℓ E Y) =
            (residueExchangeRestrictPullIso ℓ E f).hom.app
                ((residueExchangeReduction ℓ E Y).obj M) ≫
              (residueExchangeRestriction ℓ E X).map
                (((residueExchangePullComparisons ℓ E).pull f).inv.app M) ≫
              (residueExchangeTensorPullIso ℓ E f).hom.app
                ((residueExchangeUpperStar (integralCoeff ℓ E) f).obj M) := by
  let hFlat := integralResidue_pullback_preservesFlat ℓ E f
  refine ⟨hFlat, ?_⟩
  let := residueExchangePullMonoidal ℓ E f
    (residueExchangeOrdinaryPullMonoidal ℓ E f) hFlat
  let F := residueExchangeUpperStar (integralCoeff ℓ E) f
  let RY := residueExchangeReduction ℓ E Y ⋙ residueExchangeRestriction ℓ E Y
  let B := F.obj (residueExchangeCoefficient ℓ E Y)
  let α : RY ⋙ F ⟶ F ⋙ tensorRight B :=
    Functor.whiskerRight (residueExchangeTensorIso ℓ E Y).hom F ≫
      rightTensorComparison F (residueExchangeCoefficient ℓ E Y)
  let β : RY ⋙ F ⟶ F ⋙ tensorRight B :=
    (Functor.whiskerLeft (residueExchangeReduction ℓ E Y)
      (residueExchangeRestrictPullIso ℓ E f).hom) ≫
    (Functor.whiskerRight ((residueExchangePullComparisons ℓ E).pull f).inv
      (residueExchangeRestriction ℓ E X)) ≫
    (Functor.whiskerLeft F (residueExchangeTensorPullIso ℓ E f).hom)
  intro M
  obtain ⟨P, hP, ⟨e⟩⟩ :=
    CategoryTheory.Functor.exists_kFlatMap_iso (f)^*⟦integralCoeff ℓ E⟧ M
  have h : α.app (DerivedCategory.Qh.obj P) = β.app (DerivedCategory.Qh.obj P) := by
    have : IsIso (residueExchangeTensorModelTarget ℓ E f P) := by
      let : BraidedCategory (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
        AlgebraicGeometry.ProEtale.sheafBraidedCategory Ab.{u + 1} X
      let : BraidedCategory (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) :=
        AlgebraicGeometry.ProEtale.sheafBraidedCategory Ab.{u + 1} Y
      delta residueExchangeTensorModelTarget residueExchangeUpperStar
        residueExchangeUpperStarCounit
      simpa only [Functor.tensorModelTarget, id] using
        Functor.tensorModelTarget_isIso (f)^*⟦integralCoeff ℓ E⟧
        (residueExchangeOrdinaryCoefficient ℓ E Y) P hP
    apply (cancel_mono (residueExchangeTensorModelTarget ℓ E f P)).mp
    simpa only [α, β, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, rightTensorComparison, Category.assoc] using
        (integralResidue_tensorRoute_model ℓ E f hFlat P).trans
          (integralResidue_scalarRoute_model ℓ E f hFlat P).symm
  have hα := α.naturality e.hom
  have hβ := β.naturality e.hom
  rw [h, ← hβ] at hα
  exact (cancel_epi ((RY ⋙ F).map e.hom)).mp hα

end AlgebraicGeometry.ProEtale.CondensedRing
