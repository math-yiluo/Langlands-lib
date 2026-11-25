/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSectionsScalarHomZeroRepresentative

/-! The H-zero scalar normalization extracted from the coefficient-sections package.
(blueprint: lem-coef-derived-sections-scalar-hom-zero)
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The H-zero finite scalar comparison is the normalized adjunction transpose.
Source: Stacks 03CZ, 079P and 08JA.
Choose K-flat and K-injective representatives, identify the enriched map with the
ordinary tensor-Hom transpose, and transport degree-zero cocycles through the fixed
representative evaluation equivalences.
(blueprint: lem-coef-derived-sections-normalization-scalar-hom-zero) -/
theorem coefficientDerivedSectionsScalarHomZero
    (R : CoefficientDerivedSystemReduction l E W)
    (hF : CoefficientFiniteTensorNormalization l E W R)
    (D : CoefficientDerivedSystemScalarCoherence l E W) :
    ∀ (n : ℕ)
    (P : DerivedCategory (scalarReductionSource l E W))
    (M : normalizedDVRDerived l E W n)
    (x : (DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} 0).obj
      ((coefficientIntegralGlobalHom l E W).obj
        (op P, (coefficientFiniteDerivedRestriction l E W n).obj M))),
      coefficientFiniteHomEquiv l E W n _ _
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} 0).map
            ((coefficientIntegralSections l E W).map
                (coefficientEnrichedAdjunctionMap R.integralClosed (R.finiteClosed n)
                  (coefficientFiniteDerivedExtension l E W n)
                  (coefficientFiniteAdjunction l E W n) (R.finiteTensor n) P M) ≫
              (D.scalarSections n).hom.app
                ((coefficientFiniteInternalHom l E W n).obj
                  (op ((coefficientFiniteDerivedExtension l E W n).obj P), M))) x) =
        ((coefficientFiniteAdjunction l E W n).homEquiv P M).symm
          (coefficientIntegralHomEquiv l E W P _ x) := by
  classical
  intro n P M x
  let F := coefficientFiniteDerivedExtension l E W n
  let G := coefficientFiniteDerivedRestriction l E W n
  let HI := coefficientIntegralGlobalHom l E W
  let HF := coefficientFiniteGlobalHom l E W n
  let H₀ := DerivedCategory.homologyFunctor AddCommGrpCat.{max u (t + 1)} 0
  let κ (A : DerivedCategory (scalarReductionSource l E W))
      (B : normalizedDVRDerived l E W n) :
      HI.obj (op A, G.obj B) ⟶ HF.obj (op (F.obj A), B) :=
    (coefficientIntegralSections l E W).map
        (coefficientEnrichedAdjunctionMap R.integralClosed (R.finiteClosed n)
          F (coefficientFiniteAdjunction l E W n) (R.finiteTensor n) A B) ≫
      (D.scalarSections n).hom.app
        ((coefficientFiniteInternalHom l E W n).obj (op (F.obj A), B))
  let P₀ := DerivedCategory.Q.objPreimage P
  obtain ⟨K, q, hK, _, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (R := completedIntegralCommRingSheafUnrestricted l E W) P₀
  let := hq
  let eP : DerivedCategory.Q.obj K ≅ P :=
    asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso P
  let M₀ := DerivedCategory.Q.objPreimage M
  let eM : DerivedCategory.Q.obj M₀ ≅ M := DerivedCategory.Q.objObjPreimageIso M
  let a := eP.hom
  let b := eM.inv
  let f := Prod.mkHom a.op (G.map b)
  let g := Prod.mkHom (F.map a).op b
  let x' := H₀.map (HI.map f) x
  have hn : HI.map f ≫ κ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj M₀) =
      κ P M ≫ HF.map g := by
    have h := coefficientClosedEnriched_naturality R.integralClosed (R.finiteClosed n)
      F (coefficientFiniteAdjunction l E W n) (R.finiteTensor n)
      P (DerivedCategory.Q.obj K) M (DerivedCategory.Q.obj M₀) a b
    have h' := congrArg (fun z ↦ (coefficientIntegralSections l E W).map z) h
    simp only [Functor.map_comp] at h'
    dsimp only [κ]
    change (coefficientIntegralSections l E W).map
        ((coefficientIntegralInternalHom l E W).map f) ≫ _ = _
    rw [← Category.assoc, h', Category.assoc]
    erw [(D.scalarSections n).hom.naturality
      ((coefficientFiniteInternalHom l E W n).map g)]
    simp only [HF, coefficientFiniteGlobalHom, coefficientFiniteInternalHom,
      Functor.comp_map, Category.assoc]
  have hx : H₀.map (κ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj M₀)) x' =
      H₀.map (HF.map g) (H₀.map (κ P M) x) := by
    dsimp only [x']
    rw [← AddCommGrpCat.comp_apply, ← Functor.map_comp, hn,
      Functor.map_comp, AddCommGrpCat.comp_apply]
  have hi := (coefficientHomZeroEquiv_exists.{u, t+1, t} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)).choose_spec.1.1
  have hf := (coefficientHomZeroEquiv_exists.{u, t+1, t} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)).choose_spec.1.1
  have hix : coefficientIntegralHomEquiv l E W _ _ x' =
      a ≫ coefficientIntegralHomEquiv l E W P _ x ≫ G.map b := by
    simpa [x', H₀, HI, f, G, coefficientIntegralHomEquiv, coefficientHomZeroEquiv,
      coefficientIntegralGlobalHom, coefficientIntegralSections, Functor.comp_map] using
      hi P (G.obj M) (DerivedCategory.Q.obj K)
        (G.obj (DerivedCategory.Q.obj M₀)) a (G.map b) x
  have hfx : coefficientFiniteHomEquiv l E W n _ _
      (H₀.map (HF.map g) (H₀.map (κ P M) x)) =
      F.map a ≫ coefficientFiniteHomEquiv l E W n _ _ (H₀.map (κ P M) x) ≫ b := by
    simpa [H₀, HF, g, F, G, coefficientFiniteHomEquiv, coefficientHomZeroEquiv,
      coefficientFiniteGlobalHom, coefficientFiniteSections, Functor.comp_map] using
      hf (F.obj P) M (F.obj (DerivedCategory.Q.obj K))
        (DerivedCategory.Q.obj M₀) (F.map a) b (H₀.map (κ P M) x)
  have hr := coefficientDerivedSectionsScalarHomZero_representative l E W R hF D n
    K hK M₀ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj M₀) rfl rfl x'
  change coefficientFiniteHomEquiv l E W n _ _
      (H₀.map (κ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj M₀)) x') = _ at hr
  rw [hx, hfx, hix] at hr
  dsimp only [G] at hr
  rw [(coefficientFiniteAdjunction l E W n).homEquiv_naturality_left_symm,
    (coefficientFiniteAdjunction l E W n).homEquiv_naturality_right_symm] at hr
  change coefficientFiniteHomEquiv l E W n _ _ (H₀.map (κ P M) x) = _
  apply (cancel_epi (F.map a)).mp
  apply (cancel_mono b).mp
  simpa only [F, Category.assoc] using hr

end WeilConjectures
