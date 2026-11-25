/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.SixFunctors.ProEtale.Adic.ExtensionByZero
public import WeilConjectures.SixFunctors.ProEtale.Adic.Localization

/-!
# The exceptional inverse image on `Dᵇc(-, ℚ̄_ℓ)`

Let `k` be an algebraically closed field with `ringChar k ≠ ℓ`. As in
`WeilConjectures.SixFunctors.ProEtale.Adic.Localization`, the stage `Dᵇc(X, ℚ̄_ℓ)` is realised in
the Bhatt–Scholze model: the full subcategory
`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructibleAdic ℓ X` of the derived category
of pro-étale sheaves of modules over the constant `ℓ`-adic sheaf `ℚ̄_ℓ,X`, of bounded complexes
with constructible cohomology sheaves.

For a morphism `f : X ⟶ Y` of schemes, `Y` of finite type over `k`, and a compactification
`c = (X ⟶[j] Z ⟶[g] Y)` of `f` (`j` an open immersion, `g` proper), this file constructs

* the extension by zero `j_! : Dᵇc(X, ℚ̄_ℓ) ⥤ Dᵇc(Z, ℚ̄_ℓ)`, the restriction of the levelwise
  functor of the exact `j_!`, and the adjunction `j_! ⊣ j^*`
  (`ProEtale.boundedConstructibleAdicOpenImmersionLowerShriekUpperStarAdjunction`);
* the direct image with compact support `Rf_!(c) := j_! ⋙ Rg_*`
  (`ProEtale.boundedConstructibleAdicLowerShriekOfCompactification`);
* the exceptional inverse image `Rf^!(c) := Rg^! ⋙ j^*`
  (`ProEtale.boundedConstructibleAdicUpperShriekOfCompactification`), where `Rg^!` is the right
  adjoint of `Rg_* : Dᵇc(Z, ℚ̄_ℓ) ⥤ Dᵇc(Y, ℚ̄_ℓ)`, and the adjunction `Rf_!(c) ⊣ Rf^!(c)`
  (`ProEtale.boundedConstructibleAdicUpperShriekOfCompactificationAdjunction`), the composite of
  `j_! ⊣ j^*` and `Rg_* ⊣ Rg^!`. This is blueprint `theorem-f-shriek-finite-coefficients` at the
  coefficient stage `ℚ̄_ℓ`. For the compactification chosen by `HasCompactification`, these are
  `ProEtale.boundedConstructibleAdicUpperShriek` and
  `ProEtale.boundedConstructibleAdicUpperShriekAdjunction`.

That `Rg_*` is a left adjoint on `Dᵇc(-, ℚ̄_ℓ)` for proper `g` is part of the constructible
adjunction `Rf_! ⊣ Rf^!` of blueprint `theorem-verdier-biduality`
(not proved in the project). The constructions therefore take it as an instance argument.

## Implementation notes

`Rg^!` is `Functor.rightAdjoint`, an arbitrary choice of right adjoint extracted from the
instance argument: only the adjunction should be used about it.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable {l : ℕ} [Fact l.Prime]

/-! ### The extension by zero along an open immersion -/

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The extension by zero `j_!` along a quasi-compact open immersion, applied levelwise, preserves
`Dᵇc(-, ℚ̄_ℓ)`: it is exact, so `𝓗ⁿ(j_! K) ≅ j_! 𝓗ⁿ(K)`, and the extension by zero of a
constructible sheaf is constructible
(`AlgebraicGeometry.ProEtale.IsAdicConstructibleSheaf.openImmersionLowerShriek`). -/
lemma ProEtale.DerivedCategory.boundedConstructibleAdic.mapDerivedCategory_openImmersionLowerShriek
    [QuasiCompact j] {K : DerivedCategory (ProEtale.AdicSheaf l U)}
    (hK : ProEtale.DerivedCategory.boundedConstructibleAdic l U K) :
    ProEtale.DerivedCategory.boundedConstructibleAdic l X
      ((ProEtale.adicOpenImmersionLowerShriek l j).mapDerivedCategory.obj K) :=
  ⟨Functor.bounded_mapDerivedCategory_obj _ hK.1, fun n ↦
    (ProEtale.adicConstructibleSheaf l X).prop_of_iso
      (((ProEtale.adicOpenImmersionLowerShriek l j).mapDerivedCategoryHomologyFunctorIso n).app K)
      ((hK.2 n).openImmersionLowerShriek j)⟩

variable (l) in
/-- The extension by zero `j_! : Dᵇc(U, ℚ̄_ℓ) ⥤ Dᵇc(X, ℚ̄_ℓ)` along a quasi-compact open
immersion: the restriction of the levelwise functor `D(j_!)`. -/
noncomputable abbrev ProEtale.boundedConstructibleAdicOpenImmersionLowerShriek [QuasiCompact j] :
    (ProEtale.DerivedCategory.boundedConstructibleAdic l U).FullSubcategory ⥤
      (ProEtale.DerivedCategory.boundedConstructibleAdic l X).FullSubcategory :=
  (ProEtale.DerivedCategory.boundedConstructibleAdic l U).liftFullSubcategory _
    (ProEtale.adicOpenImmersionLowerShriek l j).mapDerivedCategory
    fun _ hK ↦ hK.mapDerivedCategory_openImmersionLowerShriek j

/-- The adjunction `j_! ⊣ j^*` on `Dᵇc(-, ℚ̄_ℓ)` along a quasi-compact open immersion: the
restriction of the derived adjunction `D(j_!) ⊣ Rj^*` of the exact `j_!`
(`CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedAdjunction`), the total right derived
functor of the exact `j^*` being identified with the levelwise `D(j^*)`. -/
noncomputable def ProEtale.boundedConstructibleAdicOpenImmersionLowerShriekUpperStarAdjunction
    [QuasiCompact j] :
    ProEtale.boundedConstructibleAdicOpenImmersionLowerShriek l j ⊣
      ProEtale.boundedConstructibleAdicUpperStar l j :=
  Adjunction.restrictFullyFaithful
    ((ProEtale.adicOpenImmersionLowerShriekAdjunction l j).mapDerivedCategoryRightDerivedAdjunction
      |>.ofNatIsoRight (ProEtale.adicUpperStar l j).rightDerivedFunctorIsoMapDerivedCategory)
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _) (Iso.refl _) (Iso.refl _)

end OpenImmersion

/-! ### The direct image with compact support and the exceptional inverse image -/

section Shriek

variable {k : Type u} [Field k] [IsAlgClosed k] (hk : ringChar k ≠ l) {X Y : Scheme.{u}}
  (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] [QuasiCompact sY]

omit [IsAlgClosed k] [QuasiCompact sY] in
include sY in
/-- The open immersion of a compactification of a morphism to a scheme of finite type over `k` is
quasi-compact: the compactification is locally noetherian, being of finite type over `k`. -/
lemma Compactification.quasiCompact_i_of_locallyOfFiniteType {f : X ⟶ Y}
    (c : Compactification f) : QuasiCompact c.i :=
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian (c.g ≫ sY)
  inferInstance

section OfCompactification

variable {f : X ⟶ Y} (c : Compactification f)

/-- The direct image with compact support `Rf_!(c) := j_! ⋙ Rg_* : Dᵇc(X, ℚ̄_ℓ) ⥤ Dᵇc(Y, ℚ̄_ℓ)`
attached to a compactification `c = (X ⟶[j] Z ⟶[g] Y)` of `f`: the extension by zero along the
open immersion `j` followed by the direct image along the proper morphism `g`. -/
noncomputable def ProEtale.boundedConstructibleAdicLowerShriekOfCompactification :
    (ProEtale.DerivedCategory.boundedConstructibleAdic l X).FullSubcategory ⥤
      (ProEtale.DerivedCategory.boundedConstructibleAdic l Y).FullSubcategory :=
  have := c.quasiCompact_i_of_locallyOfFiniteType sY
  ProEtale.boundedConstructibleAdicOpenImmersionLowerShriek l c.i ⋙
    ProEtale.boundedConstructibleAdicRightDerivedLowerStar sY hk c.g

variable [(ProEtale.boundedConstructibleAdicRightDerivedLowerStar (l := l) sY hk c.g).IsLeftAdjoint]

/-- Blueprint `theorem-f-shriek-finite-coefficients` (at the coefficient stage `ℚ̄_ℓ`): the
exceptional inverse image `Rf^!(c) : Dᵇc(Y, ℚ̄_ℓ) ⥤ Dᵇc(X, ℚ̄_ℓ)` attached to a compactification
`c = (X ⟶[j] Z ⟶[g] Y)` of `f`: a right adjoint `Rg^!` of the direct image
`Rg_* : Dᵇc(Z, ℚ̄_ℓ) ⥤ Dᵇc(Y, ℚ̄_ℓ)` along the proper `g`, followed by the pullback `j^*` along the
open immersion `j`. The blueprint characterizes it by the adjunction
`Hom(Rf_! K, L) ≅ Hom(K, Rf^! L)` on `Dᵇc(-, ℚ̄_ℓ)`
(`AlgebraicGeometry.ProEtale.boundedConstructibleAdicUpperShriekOfCompactificationAdjunction`).
That `Rg_*` has a right adjoint is the instance argument; its existence is part of the
constructible adjunction of blueprint `theorem-verdier-biduality` (another subsection). -/
noncomputable def ProEtale.boundedConstructibleAdicUpperShriekOfCompactification :
    (ProEtale.DerivedCategory.boundedConstructibleAdic l Y).FullSubcategory ⥤
      (ProEtale.DerivedCategory.boundedConstructibleAdic l X).FullSubcategory :=
  (ProEtale.boundedConstructibleAdicRightDerivedLowerStar (l := l) sY hk c.g).rightAdjoint ⋙
    ProEtale.boundedConstructibleAdicUpperStar l c.i

/-- Blueprint `theorem-f-shriek-finite-coefficients` (at the coefficient stage `ℚ̄_ℓ`, the
characterizing adjunction): the adjunction `Rf_!(c) ⊣ Rf^!(c)` on `Dᵇc(-, ℚ̄_ℓ)`, the composite
of the adjunction `j_! ⊣ j^*` along the open immersion `j` and of the adjunction `Rg_* ⊣ Rg^!`
along the proper `g`. -/
noncomputable def ProEtale.boundedConstructibleAdicUpperShriekOfCompactificationAdjunction :
    ProEtale.boundedConstructibleAdicLowerShriekOfCompactification hk sY c ⊣
      ProEtale.boundedConstructibleAdicUpperShriekOfCompactification (l := l) hk sY c :=
  have := c.quasiCompact_i_of_locallyOfFiniteType sY
  (ProEtale.boundedConstructibleAdicOpenImmersionLowerShriekUpperStarAdjunction c.i).comp
    (Adjunction.ofIsLeftAdjoint _)

/-- The direct image with compact support `Rf_!(c)` on `Dᵇc(-, ℚ̄_ℓ)` is a left adjoint. -/
instance ProEtale.isLeftAdjoint_boundedConstructibleAdicLowerShriekOfCompactification :
    (ProEtale.boundedConstructibleAdicLowerShriekOfCompactification (l := l) hk sY
      c).IsLeftAdjoint :=
  (ProEtale.boundedConstructibleAdicUpperShriekOfCompactificationAdjunction hk sY c).isLeftAdjoint

end OfCompactification


section Chosen

variable (f : X ⟶ Y) [HasCompactification f]
  [(ProEtale.boundedConstructibleAdicRightDerivedLowerStar (l := l) sY hk
    (HasCompactification.compactification f).g).IsLeftAdjoint]

/-- Blueprint `theorem-f-shriek-finite-coefficients` (at the coefficient stage `ℚ̄_ℓ`): the
exceptional inverse image `Rf^! : Dᵇc(Y, ℚ̄_ℓ) ⥤ Dᵇc(X, ℚ̄_ℓ)` along `f`, the functor
`ProEtale.boundedConstructibleAdicUpperShriekOfCompactification` attached to the chosen
compactification `HasCompactification.compactification f`. -/
noncomputable def ProEtale.boundedConstructibleAdicUpperShriek :
    (ProEtale.DerivedCategory.boundedConstructibleAdic l Y).FullSubcategory ⥤
      (ProEtale.DerivedCategory.boundedConstructibleAdic l X).FullSubcategory :=
  ProEtale.boundedConstructibleAdicUpperShriekOfCompactification hk sY
    (HasCompactification.compactification f)

/-- Blueprint `theorem-f-shriek-finite-coefficients` (at the coefficient stage `ℚ̄_ℓ`, the
characterizing adjunction): the adjunction `Rf_! ⊣ Rf^!` on `Dᵇc(-, ℚ̄_ℓ)` for the chosen
compactification of `f`. -/
noncomputable def ProEtale.boundedConstructibleAdicUpperShriekAdjunction :
    ProEtale.boundedConstructibleAdicLowerShriekOfCompactification hk sY
        (HasCompactification.compactification f) ⊣
      ProEtale.boundedConstructibleAdicUpperShriek (l := l) hk sY f :=
  ProEtale.boundedConstructibleAdicUpperShriekOfCompactificationAdjunction hk sY _

end Chosen
end Shriek

end AlgebraicGeometry
