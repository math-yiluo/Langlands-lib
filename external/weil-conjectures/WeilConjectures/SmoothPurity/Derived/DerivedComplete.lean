/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralReductionTower
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence

/-!
# Derived complete objects for completed integral pro-etale coefficients

Source: Weil conjectures blueprint, `chap-Smooth-purity`, `sk-def-sf-operations`,
node `def-weil-derived-complete`; Bhatt--Scholze, Definition 3.5.2
(blueprint: def-weil-derived-complete).

The definition asks for a K-flat representative of an object whose augmented reduction
tower is a homotopy-limit cone. The cone legs are the canonical reduction maps supplied
by `integralReductionTowerCone`; its Milnor triangle is therefore the Roos triangle
with first map `c : K → ∏ₙ Kₙ` and transition `1 - s`.
The bounded integral constructibility interface imports this same definition through
a paired source overlay. This keeps its canonical coefficient and K-flat interfaces
consistent when published compiled artifacts lag behind their recorded sources.
The integral triangulation statement compiles this same canonical interface in a
paired source packet to retain its recorded independent coefficient universes.
-/

@[expose] public section

set_option autoImplicit false

universe d t u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

/-- An object of `D(Y_proet, O_E)` is derived complete when its canonical reduction
  tower is a homotopy-limit tower. For a representative `G` of the object, choose a
  K-flat resolution `q : P ⟶ G`; `integralReductionTowerCone q hq` has point `Q.obj G`
  and legs the canonical maps `c_n : Q.obj G ⟶ K_n`. Thus its homotopy-limit condition
  is exactly the distinguished Roos triangle
  `K → ∏ₙ K_n →^{1-s} ∏ₙ K_n → K[1]`. The existential is independent of the chosen
  representative by the recorded well-definedness theorem for the reduction tower.
  Source: Bhatt--Scholze, Definition 3.5.2, p. 24; Stacks Tag 06YL
  (blueprint: def-weil-derived-complete). -/
noncomputable def IsDerivedComplete
    (K : completedIntegralDerivedCategory l E Y D hl) : Prop :=
  ∃ (P G : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
    (q : P ⟶ G)
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q)
    (e : DerivedCategory.Q.obj G ≅ K),
    let F := integralReductionTower l E Y D hl P
    let c := (integralReductionTowerCone l E Y D hl q hq).extend e.inv
    ∃ hprod : HasProduct (fun n : ℕ ↦ F.obj (op n)),
      letI := hprod
      ∃ δ : (∏ᶜ fun n : ℕ ↦ F.obj (op n)) ⟶ K⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle (fun n : ℕ ↦ F.map (homOfLE n.le_succ).op) K
          (Pi.lift (fun n : ℕ ↦ c.π.app (op n))) δ

end WeilConjectures
