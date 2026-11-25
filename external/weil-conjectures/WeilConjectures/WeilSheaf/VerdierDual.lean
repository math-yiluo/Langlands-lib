/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import WeilConjectures.WeilSheaf.DerivedHom
public import WeilConjectures.WeilSheaf.DerivedHomTriangulated
public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
public import WeilConjectures.WeilSheaf.TateTwist
public import WeilConjectures.WeilSheaf.UpperShriek
import WeilConjectures.WeilSheaf.Bidual
import WeilConjectures.WeilSheaf.DerivedHomSingleResolution
import WeilConjectures.WeilSheaf.SmoothPurity
import WeilConjectures.WeilSheaf.SmoothPurityAbsolute
import WeilConjectures.CategoryTheory.Adjunction.DualityConjugate
import WeilConjectures.WeilSheaf.SmoothPurityAbsolute
import WeilConjectures.WeilSheaf.VerdierExchangeNatural
import WeilConjectures.WeilSheaf.VerdierBiduality

/-!
# The exceptional inverse image and the Verdier dual of Weil complexes

For a separated morphism of finite type `f : X ⟶ Y` of separated `k₀`-schemes of finite type,
the direct image with compact support `Rf₀!` of Weil complexes
(`AlgebraicGeometry.WeilComplex.derivedLowerShriek`) has a right adjoint `Rf^!` on Weil
complexes; this is the constructible adjunction `Rf_! ⊣ Rf^!` of the six-functor chapter
(`theorem-verdier-biduality`), stated in `WeilConjectures.WeilSheaf.UpperShriek` as
`AlgebraicGeometry.WeilComplex.isLeftAdjoint_derivedLowerShriek`. The exceptional inverse image
`AlgebraicGeometry.WeilComplex.upperShriek f` is *defined* as that right adjoint, which is how
the blueprint characterizes it (`theorem-f-shriek-finite-coefficients`); so that no data is chosen
from the existence statement, it takes the existence of the right adjoint
(`AlgebraicGeometry.WeilComplex.HasUpperShriek f`) as a hypothesis. It gives the dualizing
complex `ω_X = Ra_X^! ℚ̄_ℓ` (`AlgebraicGeometry.WeilComplex.dualizingComplex`) and the Verdier
dual `𝔻_X = RHom(-, ω_X)` (`AlgebraicGeometry.WeilComplex.verdierDual`), the derived internal
hom of pro-étale Weil sheaves into `ω_X` (`AlgebraicGeometry.ProEtaleWeilSheaf.derivedHom`).

The statements of the duality theory for Weil complexes that the boundary duality of
`chap-The-Deligne-Laumon-theorem-for-curves` uses belong to the chapters on the six functors and on
smooth purity; they are stated here with `sorry`, each with the blueprint node it renders:

- `theorem-verdier-biduality`: the fact that `𝔻_X` preserves Weil complexes, its exactness,
  biduality `K ≅ 𝔻_X 𝔻_X K` and `Rf^! ≅ 𝔻_X f^* 𝔻_Y`;
- `lemma-internal-adjunction-two-exchange-formulas--2`: `𝔻_Y Rf₀! ≅ Rf_* 𝔻_X`;
- `corollary-dualizing-complex-smooth-scheme--1`: `ω_X ≅ ℚ̄_ℓ(d)[2d]` for `X` smooth of
  pure dimension `d`;
- `proposition-six-operations-dctf--15`: `RHom(P, N) ≅ P^∨ ⊗ N` for a lisse `P` (the biduality
  `P ≅ P^∨∨` is proved in `WeilConjectures.WeilSheaf.Bidual`);
- `lemma-local-cohomology-right-adjoint--2`, clause (4): `Ri^! Rj_* = 0` and the unit
  `Q ⟶ Ri^! Ri_* Q` is an isomorphism, for complementary immersions `i` and `j`.

All isomorphisms are stated as the existence of an isomorphism, as in
`WeilConjectures.WeilSheaf.LowerShriekFunctoriality`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace WeilComplex

section VerdierDual

variable (k₀ l) (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [HasUpperShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))]

/-- The dualizing complex `ω_X = Ra_X^! ℚ̄_ℓ` of a separated `k₀`-scheme of finite type `X`: the
exceptional inverse image of the constant Weil sheaf `ℚ̄_ℓ` on `Spec k₀` along the structure
morphism (blueprint: `theorem-verdier-biduality`,
`lemma-internal-adjunction-two-exchange-formulas--2`). -/
noncomputable def dualizingComplex : WeilComplex k₀ l X :=
  (upperShriek (X ↘ Spec (CommRingCat.of k₀))).obj
    (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l (Spec (CommRingCat.of k₀))))

variable {X} in
/-- **The Verdier dual preserves Weil complexes** (blueprint: `theorem-verdier-biduality`, the
duality `D_{X,ℚ̄_ℓ} : D^b_c(X, ℚ̄_ℓ)ᵒᵖ ⥤ D^b_c(X, ℚ̄_ℓ)` is the internal hom into
`ω_{X,ℚ̄_ℓ} = Ra_X^! ℚ̄_ℓ`): the derived internal hom `RHom(K, ω_X)` of a Weil complex `K` into
the dualizing complex is a Weil complex. -/
theorem objectProperty_derivedHom_dualizingComplex (K : WeilComplex k₀ l X) :
    WeilComplex.objectProperty k₀ l X
      ((ProEtaleWeilSheaf.derivedHom k₀ l X (dualizingComplex k₀ l X).obj).obj (op K.obj)) :=
  objectProperty_derivedHom K (dualizingComplex k₀ l X)

/-- The Verdier dual `𝔻_X K = RHom(K, ω_X)` of Weil complexes on a separated `k₀`-scheme of
finite type `X`, the derived internal hom into the dualizing complex
(blueprint: `theorem-verdier-biduality`, `lemma-internal-adjunction-two-exchange-formulas--2`). -/
noncomputable def verdierDual : (WeilComplex k₀ l X)ᵒᵖ ⥤ WeilComplex k₀ l X :=
  ObjectProperty.lift _
    ((ObjectProperty.ι _).op ⋙ ProEtaleWeilSheaf.derivedHom k₀ l X (dualizingComplex k₀ l X).obj)
    fun K ↦ objectProperty_derivedHom_dualizingComplex k₀ l K.unop

@[simp]
lemma verdierDual_obj_obj (K : (WeilComplex k₀ l X)ᵒᵖ) :
    ((verdierDual k₀ l X).obj K).obj =
      (ProEtaleWeilSheaf.derivedHom k₀ l X (dualizingComplex k₀ l X).obj).obj (op K.unop.obj) :=
  rfl

/-- **Verdier biduality** (blueprint: `theorem-verdier-biduality`, "evaluation and biduality
descend, giving a natural isomorphism `K ≅ D_{X,ℚ̄_ℓ} D_{X,ℚ̄_ℓ} K`"). -/
theorem nonempty_iso_verdierDual_rightOp_comp_verdierDual :
    Nonempty (𝟭 (WeilComplex k₀ l X) ≅ (verdierDual k₀ l X).rightOp ⋙ verdierDual k₀ l X) :=
  nonempty_iso_dual_rightOp_comp_dual (dualizingComplex k₀ l X)
    (nonempty_nativeGeometricForget_obj_iso_of_adjunction
      (derivedLowerShriekUpperShriekAdjunction _))

open Pretriangulated.Opposite in
/-- **The Verdier dual is exact** (blueprint: `theorem-verdier-biduality`, "an exact
`ℚ̄_ℓ`-linear anti-equivalence `D_{X,ℚ̄_ℓ}`"): it commutes with the shifts and carries distinguished
triangles of `(WeilComplex X)ᵒᵖ` to distinguished triangles. -/
theorem exists_commShift_isTriangulated_verdierDual :
    ∃ _ : (verdierDual k₀ l X).CommShift ℤ, (verdierDual k₀ l X).IsTriangulated := by
  obtain ⟨_, _⟩ := DerivedCategory.exists_commShift_isTriangulated_bifunctorRHom
    (ProEtaleWeilSheaf.ihomBifunctor k₀ l X) (dualizingComplex k₀ l X).obj
  unfold verdierDual ProEtaleWeilSheaf.derivedHom
  exact ⟨Functor.CommShift.ofComp ((WeilComplex.objectProperty k₀ l X).liftCompιIso _ _) ℤ,
    ObjectProperty.isTriangulated_lift _ _ _⟩

end VerdierDual

section Exchange

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))] (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [HasUpperShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))]
  [HasUpperShriek k₀ l (Y ↘ Spec (CommRingCat.of k₀))]

/-- **The exceptional inverse image as a conjugate of the pullback** (blueprint:
`theorem-verdier-biduality`, "`Rf^! = D_X f^* D_Y`"): `Rf^! L ≅ 𝔻_X f^* 𝔻_Y L`. -/
theorem nonempty_upperShriek_obj_iso [HasUpperShriek k₀ l f] (L : WeilComplex k₀ l Y) :
    Nonempty ((upperShriek f).obj L ≅
      (verdierDual k₀ l X).obj (op ((upperStar f).obj ((verdierDual k₀ l Y).obj (op L))))) := by
  obtain ⟨eX⟩ := nonempty_iso_verdierDual_rightOp_comp_verdierDual k₀ l X
  obtain ⟨eY⟩ := nonempty_iso_verdierDual_rightOp_comp_verdierDual k₀ l Y
  obtain ⟨ex⟩ := nonempty_verdierDual_derivedLowerShriek_natIso f
    (objectProperty_derivedHom_dualizingComplex k₀ l)
    (objectProperty_derivedHom_dualizingComplex k₀ l)
  obtain ⟨e⟩ := Adjunction.nonempty_iso_rightOp_comp_op_comp_of_duality (verdierDual k₀ l X) eX
    (verdierDual k₀ l Y) eY (upperStarDerivedLowerStarAdjunction f)
    (derivedLowerShriekUpperShriekAdjunction f) ex
  exact ⟨e.app L⟩

/-- **Verdier exchange** (blueprint: `lemma-internal-adjunction-two-exchange-formulas--2`): for a
separated morphism of finite type `f : X ⟶ Y`, `𝔻_Y (Rf₀! M) ≅ Rf_* (𝔻_X M)`. -/
theorem nonempty_verdierDual_derivedLowerShriek_iso (M : WeilComplex k₀ l X) :
    Nonempty ((verdierDual k₀ l Y).obj (op ((derivedLowerShriek k₀ l f).obj M)) ≅
      (derivedLowerStar f).obj ((verdierDual k₀ l X).obj (op M))) :=
  ⟨(nonempty_verdierDual_derivedLowerShriek_natIso f
    (objectProperty_derivedHom_dualizingComplex k₀ l)
    (objectProperty_derivedHom_dualizingComplex k₀ l)).some.app (op M)⟩

end Exchange

section Smooth

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [HasUpperShriek k₀ l (X ↘ Spec (CommRingCat.of k₀))]

/-- **The dualizing complex of a smooth scheme** (blueprint:
`corollary-dualizing-complex-smooth-scheme--1`, at the coefficient stage `ℚ̄_ℓ`): if `X`
is smooth of pure dimension `d` over `k₀`, then `ω_X ≅ ℚ̄_ℓ(d)[2d]`. -/
theorem nonempty_dualizingComplex_iso (d : ℕ)
    [SmoothOfRelativeDimension d (X ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (dualizingComplex k₀ l X ≅
      ((tateTwist k₀ l X d).obj
        (WeilSheaf.toComplex.obj (WeilSheaf.adicConstant k₀ l X)))⟦(2 * d : ℤ)⟧) :=
  purity_nonempty_shriekRightAdjoint_adicConstant_iso d
    (derivedLowerShriekUpperShriekAdjunction _)

end Smooth

section Lisse

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]

/-- **The internal hom out of a lisse sheaf** (blueprint: `proposition-six-operations-dctf--15`):
for a lisse Weil sheaf `P`, a locally free `ℚ̄_ℓ,X̄`-module of finite rank, and a Weil complex `N`,
`P^∨ ⊗ N` and `RHom(P, N)` are isomorphic. The blueprint asserts that the canonical map
`P^∨ ⊗ N ⟶ RHom(P, N)` is an isomorphism; only the existence of an isomorphism is stated here. -/
theorem nonempty_tensorLisse_dual_iso_derivedHom (P : WeilSheaf k₀ l X) (hP : P.IsLisse)
    (N : WeilComplex k₀ l X) :
    Nonempty (((tensorLisse (P.dual hP) hP.dual).obj N).obj ≅
      (ProEtaleWeilSheaf.derivedHom k₀ l X N.obj).obj (op (WeilSheaf.toComplex.obj P).obj)) := by
  obtain ⟨e⟩ := WeilSheaf.nonempty_iso_dual_dual P hP
  obtain ⟨c, _, _, _, hc⟩ :=
    ProEtaleWeilSheaf.derivedHom_single_resolution (k₀ := k₀) (l := l) (X := X)
  obtain ⟨d, _⟩ := hc P.obj N.obj N.property.1.1
  let e' := (WeilSheaf.objectProperty k₀ l X).ι.mapIso e
  let h := (ProEtaleWeilSheaf.ihomBifunctor k₀ l X).mapIso e'.op
  exact ⟨(Functor.rightDerivedFunctorNatIso h).app N.obj ≪≫ d.symm⟩

end Lisse

end WeilComplex

end AlgebraicGeometry
