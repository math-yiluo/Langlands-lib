/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportIntegralScalarMorphism
public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeCompactSupportScalarTransitions
public import WeilConjectures.SixFunctors.LocallyFiniteAdicCompactSupport.NativeIntegralScalarBoundaryConditions

/-! # Integral scalar-mate steps for native compact support -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped Obj
namespace WeilConjectures.LocallyFiniteAdicCompactSupport
open LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open ConstructibleExceptionalCoefficients
variable (l : ℕ) [Fact l.Prime]
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  {f : X ⟶ Y} [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (P : CoefficientConstruction l (ULift.{u} (PadicAlgCl l)) D hl (f := f))
  (c : Compactification f)

private theorem cast_arrow_heq {C : Type*} [Category C]
    {A B A' B' : C} (f : A' ⟶ B') (hA : A = A') (hB : B' = B) :
    ArrowHEq (eqToHom hA ≫ f ≫ eqToHom hB) f := by
  cases hA
  cases hB
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using ArrowHEq.refl f

private theorem sixArrow_regroup {C : Type*} [Category C]
    {A B C' D E F G : C} (a₀ : A ⟶ B) (a₁ : B ⟶ C') (a₂ : C' ⟶ D)
    (a₃ : D ⟶ E) (a₄ : E ⟶ F) (a₅ : F ⟶ G) :
    a₀ ≫ a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ a₅ = (a₀ ≫ a₁ ≫ a₂) ≫ a₃ ≫ (a₄ ≫ a₅) := by
  simp only [Category.assoc]

/-- Endpoint-aware integral normalization uniquely factors through its two boundaries.
Source: Bhatt--Scholze, Remark 6.8.15.
Proof: compare the rational arrows using their common prescribed value, then map
that equality through inclusion, realization and derived sections. Compare the other
five arrows with their prescribed values. Their endpoint equations let these six
arrow equalities be composed. The given boundary equations regroup the first three
and last two factors. Coefficient equality transports insert only equality arrows.
(blueprint: lem-sf-native-integral-scalar-component-factorization). -/
theorem integralComponent_factorization [G : NativeGeometry.{u} l]
    (source : Realization l X) (target : Realization l Y)
    (E : Index l (PadicAlgCl l))
    (change : ∀ j : Index l (PadicAlgCl l),
      PurCompactSupport.Change (PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) j)) (nativeCoefficients l))
    (hs : (change E).map X = (source.coefficient E).integralMap l X)
    (ht : (change E).map Y = (target.coefficient E).integralMap l Y)
    (K : finiteTorConstructibleIntegralCategory l (Coefficient.{u} l (PadicAlgCl l) E) X)
    {U V : DerivedCategory (ProEtale.AdicSheaf l Y)} (m : U ⟶ V)
    (b : (sections l Y).mapDerivedCategory.obj U ⟶
      (PurCompactSupport.image (PurCompactSupport.completed l
        (Coefficient.{u} l (PadicAlgCl l) E)) c ⋙
        pbcDerivedExtend ((target.coefficient E).integralMap l Y)).obj K.obj)
    (d : (pbcDerivedExtend ((source.coefficient E).integralMap l X) ⋙
      PurCompactSupport.image (nativeCoefficients l) c).obj K.obj ⟶
      (sections l Y).mapDerivedCategory.obj V)
    (hb : IntegralSourceBoundary l D hl P c target E K b)
    (hd : IntegralTargetBoundary l c source E K d)
    (hm : IntegralComponent l D hl P c source target change E K m) :
    (sections l Y).mapDerivedCategory.map m =
      b ≫ nativeScalarComponent l c source target E (change E) hs ht K.obj ≫ d := by
  rcases hm with ⟨A, B, r, hr, M₁, M₂, M₃, M₄, M₅,
    a₀, a₁, a₂, a₃, a₄, a₅, h₀, h₁, h₂, h₃, h₄, h₅, hm⟩
  rcases hb with ⟨Ab, Bb, rb, hrb, N₁, N₂, b₀, b₁, b₂, hb₀, hb₁, hb₂, hb⟩
  rcases hd with ⟨N₅, d₄, d₅, hd₄, hd₅, hd⟩
  have hrr := hr.trans hrb.symm
  have hrr' := (((hrr.map
    (GeneralAlgebraicallyClosedCoefficients.inclusion
      (l := l) (Ω := PadicAlgCl l) (Y := Y) E)).map target.J).map
        (sections l Y).mapDerivedCategory)
  have hzero := h₀.trans (hrr'.trans hb₀.symm)
  have hone := h₁.trans hb₁.symm
  have htwo := h₂.trans hb₂.symm
  have hthree : ArrowHEq a₃
      (nativeScalarComponent l c source target E (change E) hs ht K.obj) :=
    h₃.trans (cast_arrow_heq _ _ _).symm
  have hfour := h₄.trans hd₄.symm
  have hfive := h₅.trans hd₅.symm
  have hh := hzero.comp (hone.comp (htwo.comp (hthree.comp (hfour.comp hfive))))
  rw [hb, hd]
  exact (hm.trans (eq_of_heq hh.heq)).trans
    (sixArrow_regroup b₀ b₁ b₂ _ d₄ d₅)

end WeilConjectures.LocallyFiniteAdicCompactSupport
