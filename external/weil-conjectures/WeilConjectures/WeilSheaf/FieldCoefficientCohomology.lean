/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.Defs
public import WeilConjectures.NumberTheory.Padics.Extension
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.OpenImmersion
public import WeilConjectures.WeilSheaf.FieldCoefficient
public import WeilConjectures.WeilSheaf.TateTwist

/-!
# Ordinary and compactly supported cohomology with coefficients in a finite extension of `ℚ_ℓ`

Let `Λ` be a commutative ring with an ultrametric norm; the cases of the blueprint are a finite
extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ` and its ring of integers `𝒪_E`, whose constant sheaf
`𝒪̂_{E,Y} : U ↦ C(U, 𝒪_E)` is the completed coefficient sheaf of Bhatt–Scholze. Let
`a : Y ⟶ s` be a morphism of schemes, in the blueprint the structure morphism of a separated
scheme of finite type over `s = Spec k`, `k` algebraically closed.
Following blueprint `def-weil-ordinary-compact-cohomology`, the coefficient complexes of
`K ∈ D(Y_proét, Λ)` are

`RΓ(Y, K) = Fib_s(Ra_* K)`, `RΓ_c(Y, K) = Fib_s(Ra_! K)`,

and `Hⁱ(Y, K)`, `Hⁱ_c(Y, K)` are their cohomology groups. Here `Ra_*` is the total right derived
functor of the pushforward of `Λ_Y`-modules, `Ra_! = Rḡ_* ∘ ī_!` for a compactification
`Y ⟶[ī] Z ⟶[ḡ] s` of `a` (an open immersion followed by a proper morphism), and `Fib_s`, the
evaluation at the geometric point of `s`, is the right derived functor of the sections over the
final object of the pro-étale site of `s`
(`AlgebraicGeometry.ProEtale.fieldGlobalSections`), with values in the derived category of
`Λ`-vector spaces.

For a constructible `Λ`-Weil sheaf or an object of `D^b_{c,W}(X, Λ)` on a `k₀`-scheme `X`, these
are applied to the underlying complex `For(K)` on the geometric fiber `X̄`
(`AlgebraicGeometry.FieldWeilComplex.cohomology`,
`AlgebraicGeometry.FieldWeilComplex.compactlySupportedCohomology`).

The coefficient object `Λ_Y` is the constant sheaf, with its canonical Weil structure
(`AlgebraicGeometry.FieldWeilSheaf.constant`), and for `Λ = E ⊆ ℚ̄_ℓ` its Tate twist `E_Y(m)`
(`AlgebraicGeometry.FieldWeilSheaf.tateTwistConstant`) is the constant sheaf whose Weil
structure is multiplied by `χ_ℓ(σ)ᵐ`, `χ_ℓ` the `ℓ`-adic cyclotomic character and `σ` the
geometric Frobenius of `k̄`: as for `ℚ̄_ℓ` (`WeilConjectures.WeilSheaf.TateTwist`), the Tate
sheaf `E(1) = ℤ_ℓ(1) ⊗ E` is constant on the geometric fiber, with the geometric Frobenius acting
on `ℤ_ℓ(1)(k̄)` by `χ_ℓ(σ) = q⁻¹`. Then `Hⁱ(Y, E(m)) = Hⁱ(Y, For(E_Y(m)))`, and similarly with
compact support.

The finite stage `A_{E,n}` is `AlgebraicGeometry.Etale.cohomology` and
`AlgebraicGeometry.Etale.compactlySupportedCohomology`, the stage `ℚ̄_ℓ` is
`AlgebraicGeometry.WeilComplex.cohomology` and
`AlgebraicGeometry.WeilComplex.compactlySupportedCohomology`.

## Main definitions

- `AlgebraicGeometry.ProEtale.fieldRightDerivedGlobalSections`,
  `AlgebraicGeometry.ProEtale.fieldCohomology`: `RΓ(Y, -)` and `Hⁱ(Y, -)`.
- `AlgebraicGeometry.ProEtale.fieldCompactlySupportedGlobalSections`,
  `AlgebraicGeometry.ProEtale.fieldCompactlySupportedCohomology`: `RΓ_c(Y, -)` and `Hⁱ_c(Y, -)`.
- `AlgebraicGeometry.FieldWeilSheaf.constant`, `AlgebraicGeometry.FieldWeilSheaf.constantTwist`,
  `AlgebraicGeometry.FieldWeilSheaf.tateTwistConstant`: `Λ_Y`, constant twists, `E_Y(m)`.
- `AlgebraicGeometry.FieldWeilComplex.cohomology`,
  `AlgebraicGeometry.FieldWeilComplex.compactlySupportedCohomology`: the cohomology of Weil
  complexes.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Endofunctor

namespace AlgebraicGeometry

namespace ProEtale

variable (Λ : Type) [NormedCommRing Λ] [IsUltrametricDist Λ]

namespace FieldSheaf

variable {Λ}

/-- Multiplication by a unit `b` of `Λ`, as an automorphism of a sheaf of `Λ_X`-modules. -/
noncomputable def smulIso {X : Scheme.{u}} (b : Λˣ) (M : FieldSheaf Λ X) : M ≅ M where
  hom := smul (ULift.up (b : Λ)) M
  inv := smul (ULift.up ((b⁻¹ : Λˣ) : Λ)) M
  hom_inv_id := by
    rw [smul_smul, ← smul_one]
    exact congrArg (smul · M) (congrArg ULift.up (Units.inv_mul b))
  inv_hom_id := by
    rw [smul_smul, ← smul_one]
    exact congrArg (smul · M) (congrArg ULift.up (Units.mul_inv b))

end FieldSheaf

/-- The sections over the final object `X` of the small pro-étale site of `X`, as a functor from
sheaves of `Λ_X`-modules to `Λ`-vector spaces. For `X = Spec k` with `k` algebraically closed,
every pro-étale cover of `X` splits, and this is the evaluation at the geometric point of `X`. -/
noncomputable def fieldGlobalSections (X : Scheme.{u}) :
    FieldSheaf Λ X ⥤ ModuleCat.{u + 1} (ULift.{u + 1} Λ) :=
  FieldSheaf.forget X ⋙ sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 X)))

instance (X : Scheme.{u}) : (fieldGlobalSections Λ X).Additive :=
  inferInstanceAs (FieldSheaf.forget X ⋙ sheafToPresheaf _ _ ⋙ _).Additive

variable {Λ} {Y s : Scheme.{u}} (a : Y ⟶ s)

/-- Blueprint `def-weil-ordinary-compact-cohomology`: Ordinary and compactly supported
cohomology, stage `Λ = E`.

The coefficient complex `RΓ(Y, K) = Fib_s(Ra_* K)` of a complex `K` of sheaves of
`Λ_Y`-modules on the pro-étale site of `Y`, along `a : Y ⟶ s`: the total right derived functor
of the pushforward `a_*`, followed by the evaluation `Fib_s` at the geometric point of `s`, the
right derived functor of the sections over the final object
(`AlgebraicGeometry.ProEtale.fieldGlobalSections`). For `Λ = E` a finite extension of `ℚ_ℓ` and
`a` the structure morphism of a separated `k`-scheme of finite type, `k` algebraically closed,
this is the `RΓ(Y, K)` of the blueprint; its cohomology is
`AlgebraicGeometry.ProEtale.fieldCohomology`. -/
noncomputable def fieldRightDerivedGlobalSections :
    _root_.DerivedCategory (FieldSheaf Λ Y) ⥤
      _root_.DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} Λ)) :=
  (fieldLowerStar Λ a).rightDerivedFunctor ⋙ (fieldGlobalSections Λ s).rightDerivedFunctor

/-- Blueprint `def-weil-ordinary-compact-cohomology`, stage `Λ = E`: the cohomology
`Hⁱ(Y, K) = Hⁱ(RΓ(Y, K))`. -/
noncomputable def fieldCohomology (i : ℤ) :
    _root_.DerivedCategory (FieldSheaf Λ Y) ⥤ ModuleCat.{u + 1} (ULift.{u + 1} Λ) :=
  fieldRightDerivedGlobalSections a ⋙ _root_.DerivedCategory.homologyFunctor _ i

/-- The direct image with compact support `Ra_! = Rḡ_* ∘ ī_!` attached to a compactification
`Y ⟶[ī] Z ⟶[ḡ] s` of `a`: the exact extension by zero along the open immersion `ī`, followed by
the total right derived functor of the pushforward along the proper morphism `ḡ`. -/
noncomputable def fieldRightDerivedLowerShriek (c : Compactification a) :
    _root_.DerivedCategory (FieldSheaf Λ Y) ⥤ _root_.DerivedCategory (FieldSheaf Λ s) :=
  (fieldOpenImmersionLowerShriek Λ c.i).mapDerivedCategory ⋙
    (fieldLowerStar Λ c.g).rightDerivedFunctor

/-- Blueprint `def-weil-ordinary-compact-cohomology`: Ordinary and compactly supported
cohomology, stage `Λ = E`.

The compactly supported coefficient complex `RΓ_c(Y, K) = Fib_s(Ra_! K)` of a complex `K` of
sheaves of `Λ_Y`-modules on the pro-étale site of `Y`, along a morphism `a : Y ⟶ s` admitting a
compactification: the direct image with compact support `Ra_! = Rḡ_* ∘ ī_!` for the chosen
compactification (`AlgebraicGeometry.ProEtale.fieldRightDerivedLowerShriek`), followed by the
evaluation `Fib_s` at the geometric point of `s`. Its cohomology is
`AlgebraicGeometry.ProEtale.fieldCompactlySupportedCohomology`. -/
noncomputable def fieldCompactlySupportedGlobalSections [HasCompactification a] :
    _root_.DerivedCategory (FieldSheaf Λ Y) ⥤
      _root_.DerivedCategory (ModuleCat.{u + 1} (ULift.{u + 1} Λ)) :=
  fieldRightDerivedLowerShriek a (HasCompactification.compactification a) ⋙
    (fieldGlobalSections Λ s).rightDerivedFunctor

/-- Blueprint `def-weil-ordinary-compact-cohomology`, stage `Λ = E`: the compactly supported
cohomology `Hⁱ_c(Y, K) = Hⁱ(RΓ_c(Y, K))`. -/
noncomputable def fieldCompactlySupportedCohomology [HasCompactification a] (i : ℤ) :
    _root_.DerivedCategory (FieldSheaf Λ Y) ⥤ ModuleCat.{u + 1} (ULift.{u + 1} Λ) :=
  fieldCompactlySupportedGlobalSections a ⋙ _root_.DerivedCategory.homologyFunctor _ i

variable (Λ) in
/-- Blueprint `def-weil-ordinary-compact-cohomology`, stages `Λ = 𝒪_E, E`: the cohomology
`Hⁱ(Y, Λ) = Hⁱ(Y, Λ_Y)` with coefficients in the constant sheaf `Λ_Y` (for `Λ = 𝒪_E` the
completed coefficient sheaf `𝒪̂_{E,Y} : U ↦ C(U, 𝒪_E)` of Bhatt–Scholze), placed in degree `0`. -/
noncomputable def fieldConstantCohomology (i : ℤ) : ModuleCat.{u + 1} (ULift.{u + 1} Λ) :=
  (fieldCohomology a i).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj (FieldSheaf.unit Λ Y))

variable (Λ) in
/-- Blueprint `def-weil-ordinary-compact-cohomology`, stages `Λ = 𝒪_E, E`: the compactly
supported cohomology `Hⁱ_c(Y, Λ) = Hⁱ_c(Y, Λ_Y)` with coefficients in the constant sheaf. -/
noncomputable def fieldConstantCompactlySupportedCohomology [HasCompactification a] (i : ℤ) :
    ModuleCat.{u + 1} (ULift.{u + 1} Λ) :=
  (fieldCompactlySupportedCohomology a i).obj
    ((_root_.DerivedCategory.singleFunctor _ 0).obj (FieldSheaf.unit Λ Y))

section Integral

variable {l : ℕ} [Fact l.Prime] (E : IntermediateField ℚ_[l] (PadicAlgCl l))

/-- The ring of integers `𝒪_E` of a subfield `E` of `ℚ̄_ℓ`, with the norm restricted from
`ℚ̄_ℓ`, is ultrametric: it is a coefficient ring `Λ = 𝒪_E` of the constructions of
`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient`, with constant sheaf the completed
coefficient sheaf `𝒪̂_{E,Y} : U ↦ C(U, 𝒪_E)`. -/
instance _root_.PadicAlgCl.isUltrametricDist_integers :
    IsUltrametricDist (PadicAlgCl.integers l E) :=
  IsUltrametricDist.subtype _

/-- Blueprint `def-weil-ordinary-compact-cohomology`, stage `Λ = 𝒪_E`: the cohomology
`Hⁱ(Y, 𝒪_E)` and the compactly supported cohomology `Hⁱ_c(Y, 𝒪_E)` are
`AlgebraicGeometry.ProEtale.fieldConstantCohomology` and
`AlgebraicGeometry.ProEtale.fieldConstantCompactlySupportedCohomology` for the ring of
integers `𝒪_E = PadicAlgCl.integers ℓ E`. -/
noncomputable example [HasCompactification a] (i : ℤ) :
    ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl.integers l E)) ×
      ModuleCat.{u + 1} (ULift.{u + 1} (PadicAlgCl.integers l E)) :=
  (fieldConstantCohomology (PadicAlgCl.integers l E) a i,
    fieldConstantCompactlySupportedCohomology (PadicAlgCl.integers l E) a i)

end Integral

end ProEtale

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {Λ : Type} [NormedField Λ] [IsUltrametricDist Λ]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

namespace FieldWeilSheaf

variable (k₀ Λ X) in
/-- The constant `Λ`-Weil sheaf `Λ_X`: the constant sheaf `Λ_X̄` on the geometric fiber, with the
canonical Weil structure `Fr_X^* Λ_X̄ = (Fr_X⁻¹)_* Λ_X̄ ≅ Λ_X̄`, pulling back functions
(`AlgebraicGeometry.ProEtale.fieldLowerStarUnitIso`). It is the coefficient object `Λ_Y` of
blueprint `def-weil-ordinary-compact-cohomology`, with its canonical Weil structure. -/
noncomputable def constant : FieldWeilSheaf k₀ Λ X where
  obj := .mk (FieldSheaf.unit Λ _)
    (fieldLowerStarUnitIso Λ (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.symm)
  property := isFieldConstructibleSheaf_fieldConstantSheaf _

/-- The constant twist `F ⊗ 𝓑_b` of a constructible `Λ`-Weil sheaf by a unit `b` of `Λ`: the
same sheaf, with its Weil structure multiplied by `b`. -/
noncomputable def constantTwist (F : FieldWeilSheaf k₀ Λ X) (b : Λˣ) : FieldWeilSheaf k₀ Λ X where
  obj := .mk F.obj.carrier (F.obj.str ≪≫ FieldSheaf.smulIso b F.obj.carrier)
  property := F.property

variable {l : ℕ} [Fact l.Prime] (E : IntermediateField ℚ_[l] (PadicAlgCl l))

variable (k₀ X) in
/-- Blueprint `def-weil-ordinary-compact-cohomology`, stage `Λ = E`: the Tate twisted constant
coefficient object `E_X(m) = E_X ⊗ E(m)` for a subfield `E` of `ℚ̄_ℓ` (for instance a finite
extension of `ℚ_ℓ`) and `m ∈ ℤ`: the constant `E`-Weil sheaf `E_X` with its Weil structure
multiplied by `χ_ℓ(σ)ᵐ`, where `χ_ℓ(σ) ∈ ℤ_ℓˣ ⊆ Eˣ` is the value of the `ℓ`-adic cyclotomic
character at the geometric Frobenius `σ` of `k̄` (`AlgebraicGeometry.WeilSheaf.cyclotomicUnit`
is its image in `ℚ̄_ℓ`). The Tate sheaf `E(1) = ℤ_ℓ(1) ⊗_{ℤ_ℓ} E` is constant on the geometric
fiber, the geometric Frobenius acting on `ℤ_ℓ(1)(k̄)` by `χ_ℓ(σ)`, which is `q⁻¹` for `ℓ ≠ p`
(`AlgebraicGeometry.WeilSheaf.cyclotomicUnit_eq`). -/
noncomputable def tateTwistConstant [Fact (ringChar k₀ ≠ l)] (m : ℤ) : FieldWeilSheaf k₀ E X :=
  letI := Fintype.ofFinite k₀
  (constant k₀ E X).constantTwist
    (Units.map ((algebraMap ℚ_[l] E).comp PadicInt.Coe.ringHom).toMonoidHom
      (cyclotomicCharacter (AlgebraicClosure k₀) l
        (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k₀ (AlgebraicClosure k₀)).toRingEquiv)
      ^ m)

end FieldWeilSheaf

namespace FieldWeilComplex

variable [HasCompactification (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure]

/-- Blueprint `def-weil-ordinary-compact-cohomology`, stage `Λ = E`: the cohomology
`Hⁱ(X̄, K) = Hⁱ(X̄, For(K))` of an object `K` of `D^b_{c,W}(X, Λ)`, the cohomology along the
structure morphism `a_X̄ : X̄ ⟶ Spec k̄` of the geometric fiber of its underlying complex. -/
noncomputable def cohomology (K : FieldWeilComplex k₀ Λ X) (i : ℤ) :
    ModuleCat.{u + 1} (ULift.{u + 1} Λ) :=
  (fieldCohomology (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure i).obj
    (forget.obj K)

/-- Blueprint `def-weil-ordinary-compact-cohomology`, stage `Λ = E`: the compactly supported
cohomology `Hⁱ_c(X̄, K) = Hⁱ_c(X̄, For(K))` of an object `K` of `D^b_{c,W}(X, Λ)`, along the
structure morphism `a_X̄ : X̄ ⟶ Spec k̄` of the geometric fiber. -/
noncomputable def compactlySupportedCohomology (K : FieldWeilComplex k₀ Λ X) (i : ℤ) :
    ModuleCat.{u + 1} (ULift.{u + 1} Λ) :=
  (fieldCompactlySupportedCohomology
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure i).obj (forget.obj K)

end FieldWeilComplex

namespace FieldWeilSheaf

variable [HasCompactification (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure]

/-- Blueprint `def-weil-ordinary-compact-cohomology`, stage `Λ = E`: the cohomology
`Hⁱ(X̄, F)` of a constructible `Λ`-Weil sheaf, that of its underlying sheaf placed in degree
`0`. For `F = E_X(m)` (`AlgebraicGeometry.FieldWeilSheaf.tateTwistConstant`) this is
`Hⁱ(X̄, E(m))`. -/
noncomputable def cohomology (F : FieldWeilSheaf k₀ Λ X) (i : ℤ) :
    ModuleCat.{u + 1} (ULift.{u + 1} Λ) :=
  (fieldCohomology (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure i).obj
    ((_root_.DerivedCategory.singleFunctor _ 0).obj F.obj.carrier)

/-- Blueprint `def-weil-ordinary-compact-cohomology`, stage `Λ = E`: the compactly supported
cohomology `Hⁱ_c(X̄, F)` of a constructible `Λ`-Weil sheaf, that of its underlying sheaf placed
in degree `0`. For `F = E_X(m)` this is `Hⁱ_c(X̄, E(m))`. -/
noncomputable def compactlySupportedCohomology (F : FieldWeilSheaf k₀ Λ X) (i : ℤ) :
    ModuleCat.{u + 1} (ULift.{u + 1} Λ) :=
  (fieldCompactlySupportedCohomology
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure i).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj F.obj.carrier)

end FieldWeilSheaf

end AlgebraicGeometry
