/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.TraceClass
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import WeilConjectures.CategoryTheory.Adjunction.ConjugateHomEquiv
import WeilConjectures.TraceFormula.LocalTerm

/-!

# The supported restriction and the local term

Let `c = (C, c₁, c₂, u)` be an endocorrespondence of `(X, K)` with support map
`c = (c₁, c₂) : C ⟶ X × X`, fixed locus `ι : Fix(c) ⟶ C` and `d = ι ≫ c₁ : Fix(c) ⟶ X`, so
that the fixed square `ι ≫ c = d ≫ Δ_X` is cartesian, and put `P = K ⊠ D_X K` on `X × X`.

* The *supported class* of `u` (blueprint `lemma-local-term-restriction-map--1`, (1)) is the section
  `[u] : ℚ̄_ℓ,C ⟶ Rc^! P`, the mate of `u` read through the external duality isomorphism
  `𝓗_c(K) ≅ Rc^! P` (`Correspondence.mate`, `Correspondence.verdierDualityIso`); its cohomology
  class lives in `H⁰ RΓ(C, Rc^! P) = H⁰ RΓ_c(X × X, P)`.
* The *supported restriction* (blueprint `lemma-local-term-restriction-map--1`, (2)) is the exchange
  morphism
  ```
  ρ_P : Lι^* Rc^! P ⟶ Rd^! LΔ^* P
  ```
  (`ProEtale.CondensedRing.Correspondence.FixedLocus.supportedRestriction`), the `Lι^* ⊣ Rι_*`
  adjoint of `Rc^! P ⟶ Rc^! RΔ_* LΔ^* P ≅ Rι_* Rd^! LΔ^* P`, the unit of `LΔ^* ⊣ RΔ_*` followed
  by base change in the fixed square. Its `Rd_! ⊣ Rd^!` adjoint is the ordinary pullback along
  the diagonal of the support object `Rc_! Rc^! P ⟶ P`, followed by base change
  (`Correspondence.FixedLocus.homEquiv_symm_supportedRestriction`): this is the description of
  the blueprint, "the ordinary pullback along `b` of the support object, followed by the
  exchange morphism to local cohomology with support in the intersection". Taking sections over
  `Fix(c)`, it maps `H⁰ RΓ_c(X × X, P)` to the local cohomology `H⁰ RΓ_{Fix(c)}(X, LΔ^* P)`.
* The *evaluation* (`Correspondence.FixedLocus.supportedEvaluation`) is
  `Rd^! LΔ^* P ≅ Rd^! (K ⊗ D_X K) --Rd^! ev--> Rd^! ω_X ≅ ω_Fix(c)`.

## Main statements

- `ProEtale.CondensedRing.Correspondence.traceClass_eq_supportedRestriction`: the trace class
  `Tr_c(u)` is the composite `ℚ̄_ℓ,Fix(c) ≅ Lι^* ℚ̄_ℓ,C --Lι^*[u]--> Lι^* Rc^! P --ρ_P-->
  Rd^! LΔ^* P --ev--> ω_Fix(c)`.
- `ProEtale.CondensedRing.Correspondence.localTerm_traceClass_eq_integral_supportedRestriction`:
  the local term along an open and closed subscheme `j : B ⟶ Fix(c)` proper over `s` is the
  integral over `B` of the restriction of this composite to `B` (blueprint
  `lemma-local-term-restriction-map--1`, `lemma-local-term-restriction-map`).
- `ProEtale.CondensedRing.Correspondence.localTerm_traceClass_eq_zero_of_supportedRestriction`:
  if the supported restriction vanishes on `B`, so does the local term.

## Implementation notes

The blueprint states `lemma-local-term-restriction-map` on the strict localization `T` of
`X × X` at a fixed point `(y, y)` of the Frobenius graph of a curve, and with coefficients in a
finite `ℓ`-primary ring; the trace class of the library is defined over `ℚ̄_ℓ` on schemes of
finite type over `s`. Here the supported restriction is formed on the whole fixed locus and then
restricted to an open and closed subscheme `B` of `Fix(c)`. When `B` is the reduced point `y`
(which is the case for the Frobenius graph, blueprint `lemma-frobenius-fixed-scheme`), its
restriction to `B` is the stalk at `y`: the source `(Rc^! P)_y = RΓ_a(T, P)` is the sections with
support on the graph over the strict localization (`c` is finite), and the target
`(Rd^! LΔ^* P)_y = RΓ_y(X, LΔ^* P)` is the local cohomology at `y`, as in the blueprint. The
identity of the lemma does not use that `X` is a curve nor that `c` is a Frobenius graph; the
curve enters only through the vanishing of the supported restriction (blueprint
`lemma-vanishing-local-term-zero-stalk`). The product factors are in the order `K ⊠ D_X K` of the
library, the blueprint's lemma uses the transposed graph and `D_X K ⊠ K`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace CategoryTheory

variable {C D E F' : Type*} [Category* C] [Category* D] [Category* E] [Category* F']
  {L : C ⥤ D} {R : D ⥤ C} {S : C ⥤ E} {T : D ⥤ F'} {U : F' ⥤ E}

/-- For an adjunction `L ⊣ R` and an isomorphism `e : R ⋙ S ≅ T ⋙ U`, the image under `S` of the
adjoint `M ⟶ R N` of `g : L M ⟶ N`, followed by `e`, is the image of the unit followed by `e` and
`U (T g)`. -/
lemma Adjunction.map_homEquiv_comp_app_hom (e : R ⋙ S ≅ T ⋙ U) (adj : L ⊣ R) {M : C} {N : D}
    (g : L.obj M ⟶ N) :
    S.map (adj.homEquiv M N g) ≫ (e.app N).hom =
      S.map (adj.unit.app M) ≫ (e.app (L.obj M)).hom ≫ U.map (T.map g) := by
  rw [Adjunction.homEquiv_unit, S.map_comp, Category.assoc]
  congr 1
  exact e.hom.naturality g

/-- Abstract form of the trace class through the supported restriction: for adjunctions
`ι^* ⊣ ι_*`, `Δ^* ⊣ Δ_*` and an isomorphism `e : Δ_* ⋙ c^! ≅ d^! ⋙ ι_*`, the `ι`-adjoint of
`m ≫ m' ≫ c^! (Δ-adjoint of g) ≫ e ≫ ι_* h` is `ι^* (m ≫ m')` followed by the `ι`-adjoint of
`c^!(unit) ≫ e`, then `d^! g ≫ h`. -/
lemma Adjunction.homEquiv_symm_comp_map_homEquiv {C₁ C₂ D₁ D₂ : Type*} [Category* C₁]
    [Category* C₂] [Category* D₁] [Category* D₂] {Li : C₁ ⥤ D₁} {Ri : D₁ ⥤ C₁}
    {LΔ : C₂ ⥤ D₂} {RΔ : D₂ ⥤ C₂} {S : C₂ ⥤ C₁} {T : D₂ ⥤ D₁} (adjι : Li ⊣ Ri)
    (adjΔ : LΔ ⊣ RΔ) (e : RΔ ⋙ S ≅ T ⋙ Ri) {A Q : C₁} {P : C₂} {ω : D₂} {ω' : D₁}
    (m : A ⟶ Q) (m' : Q ⟶ S.obj P) (g : LΔ.obj P ⟶ ω) (h : T.obj ω ⟶ ω') :
    (adjι.homEquiv _ _).symm
        (m ≫ m' ≫ S.map (adjΔ.homEquiv _ _ g) ≫ (e.app ω).hom ≫ Ri.map h) =
      Li.map (m ≫ m') ≫ (adjι.homEquiv _ _).symm (S.map (adjΔ.unit.app P) ≫ (e.app _).hom) ≫
        T.map g ≫ h := by
  rw [Equiv.symm_apply_eq, Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply, Functor.map_comp,
    reassoc_of% (map_homEquiv_comp_app_hom e adjΔ g)]
  simp only [Category.assoc]


/-- Abstract form of the two descriptions of the supported restriction: for adjunctions
`c_! ⊣ c^!`, `Δ^* ⊣ Δ_*`, `ι^* ⊣ ι_*`, `d_! ⊣ d^!` and a base change isomorphism
`σ : c_! ⋙ Δ^* ≅ ι^* ⋙ d_!` with conjugate `e : Δ_* ⋙ c^! ≅ d^! ⋙ ι_*`, the `d`-adjoint of the
`ι`-adjoint of `c^!(unit) ≫ e` is `σ⁻¹` followed by `Δ^*` of the counit of `c_! ⊣ c^!`. -/
lemma Adjunction.homEquiv_symm_homEquiv_symm_map_unit_comp_conjugateIsoEquiv {C₁ C₂ C₃ C₄ : Type*}
    [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄] {A : C₁ ⥤ C₂} {A' : C₂ ⥤ C₁}
    {B : C₂ ⥤ C₃} {B' : C₃ ⥤ C₂} {E : C₁ ⥤ C₄} {E' : C₄ ⥤ C₁} {G : C₄ ⥤ C₃} {G' : C₃ ⥤ C₄}
    (a : A ⊣ A') (b : B ⊣ B') (e : E ⊣ E') (g : G ⊣ G') (σ : A ⋙ B ≅ E ⋙ G) (P : C₂) :
    (g.homEquiv _ _).symm ((e.homEquiv _ _).symm (A'.map (b.unit.app P) ≫
        ((conjugateIsoEquiv (a.comp b) (e.comp g) σ.symm).app (B.obj P)).hom)) =
      σ.inv.app (A'.obj P) ≫ B.map (a.counit.app P) := by
  rw [Equiv.symm_apply_eq, Equiv.symm_apply_eq]
  refine Eq.trans ?_ (homEquiv_homEquiv_comp_conjugateIsoEquiv_app a b e g σ
    (M := A'.obj P) (N := B.obj P) (B.map (a.counit.app P)))
  congr 1
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.unit_naturality,
    Functor.map_comp,
    Adjunction.right_triangle_components_assoc]


/-- Moving a natural isomorphism `φ : S ≅ T` past the image of a composite of four morphisms. -/
lemma Iso.inv_app_comp_map_comp {C D : Type*} [Category* C] [Category* D] {S T : C ⥤ D}
    (φ : S ≅ T) {Z : D} {A₀ A₁ A₂ A₃ A₄ : C} {W : D} (ε : Z ⟶ T.obj A₀) (a : A₀ ⟶ A₁)
    (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃) (d : A₃ ⟶ A₄) (h : S.obj A₄ ⟶ W) :
    (ε ≫ φ.inv.app A₀) ≫ S.map (a ≫ b ≫ c ≫ d) ≫ h =
      ε ≫ T.map (a ≫ b) ≫ T.map c ≫ T.map d ≫ φ.inv.app A₄ ≫ h := by
  simp only [Functor.map_comp, Category.assoc, NatTrans.naturality_assoc]


end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] {K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧}

namespace Correspondence

variable {c : Correspondence ℓ K}

namespace FixedLocus

variable (F : c.FixedLocus)

/-- The *supported restriction* `ρ_P : Lι^* Rc^! P ⟶ Rd^! LΔ^* P` (blueprint
`lemma-local-term-restriction-map--1`, (2)): the `Lι^* ⊣ Rι_*` adjoint of
```
Rc^! P ⟶ Rc^! RΔ_* LΔ^* P ≅ Rι_* Rd^! LΔ^* P,
```
the unit of `LΔ^* ⊣ RΔ_*` followed by base change in the fixed square
(`FixedLocus.upperShriekLowerStarIso`). On sections it maps the classes supported on the
support `c` of the correspondence to the local cohomology of `LΔ^* P` with support in the fixed
locus. -/
noncomputable def supportedRestriction (P : Dᵇc((X ⨯ X).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar _ ℓ F.ι).obj
        ((boundedConstructibleUpperShriek ℓ c.support).obj P) ⟶
      (boundedConstructibleUpperShriek ℓ F.d).obj
        ((boundedConstructibleUpperStar _ ℓ (diag X)).obj P) :=
  ((boundedConstructibleUpperStarLowerStarAdjunction ℓ F.ι).homEquiv _ _).symm
    ((boundedConstructibleUpperShriek ℓ c.support).map
        ((boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X)).unit.app P) ≫
      (F.upperShriekLowerStarIso.app _).hom)

/-- The *evaluation* `Rd^! LΔ^* (K ⊠ D_X K) ⟶ ω_Fix(c)` (blueprint
`lemma-local-term-restriction-map--1`): `Rd^!` of the identification
`LΔ^* (K ⊠ D_X K) ≅ K ⊗ D_X K` followed by the evaluation `K ⊗ D_X K ⟶ ω_X`, and the
composition isomorphism `Rd^! ω_X ≅ ω_Fix(c)`. -/
noncomputable def supportedEvaluation :
    (boundedConstructibleUpperShriek ℓ F.d).obj
        ((boundedConstructibleUpperStar _ ℓ (diag X)).obj
          (externalProduct ℓ K (verdierDual ℓ K))) ⟶
      dualizingComplex' ℓ F.F :=
  (boundedConstructibleUpperShriek ℓ F.d).map
      ((diagUpperStarExternalProductIso ℓ K _).hom ≫ (ihom.ev K).app (dualizingComplex' ℓ X)) ≫
    (dualizingComplexComp ℓ F.d).hom

/-- The adjoint of the supported restriction along `ι`: `Rc^! P ⟶ Rι_* Rd^! LΔ^* P` is the unit
of `LΔ^* ⊣ RΔ_*` followed by base change in the fixed square. -/
lemma homEquiv_supportedRestriction (P : Dᵇc((X ⨯ X).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStarLowerStarAdjunction ℓ F.ι).homEquiv _ _
        (F.supportedRestriction P) =
      (boundedConstructibleUpperShriek ℓ c.support).map
          ((boundedConstructibleUpperStarLowerStarAdjunction ℓ (diag X)).unit.app P) ≫
        (F.upperShriekLowerStarIso.app _).hom := by
  rw [supportedRestriction, Equiv.apply_symm_apply]


/-- **The supported restriction as a pullback of the support object** (blueprint
`lemma-local-term-restriction-map--1`, (2), second description): the `Rd_! ⊣ Rd^!` adjoint of the
supported restriction `ρ_P` is the ordinary pullback along the diagonal of the support object
`Rc_! Rc^! P ⟶ P`, read through compact-support base change `Rd_! Lι^* ≅ LΔ^* Rc_!` in the fixed
square. -/
lemma homEquiv_symm_supportedRestriction
    (P : Dᵇc((X ⨯ X).left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    ((boundedConstructibleUpperShriekAdjunction ℓ F.d).homEquiv _ _).symm
        (F.supportedRestriction P) =
      F.lowerShriekBaseChangeIso.inv.app _ ≫
        (boundedConstructibleUpperStar _ ℓ (diag X)).map
          ((boundedConstructibleUpperShriekAdjunction ℓ c.support).counit.app P) := by
  unfold supportedRestriction upperShriekLowerStarIso
  exact Adjunction.homEquiv_symm_homEquiv_symm_map_unit_comp_conjugateIsoEquiv _ _ _ _
    F.lowerShriekBaseChangeIso P

end FixedLocus

variable (c) (F : c.FixedLocus)

/-- **The trace class through the supported restriction** (blueprint
`lemma-local-term-restriction-map--1`, `lemma-local-term-restriction-map`, before
restriction to a fixed point): the trace class `Tr_c(u)` is the composite
```
ℚ̄_ℓ,Fix(c) ≅ Lι^* ℚ̄_ℓ,C --Lι^* [u]--> Lι^* Rc^! P --ρ_P--> Rd^! LΔ^* P --ev--> ω_Fix(c)
```
of the supported class `[u]` (the mate of `u` read through external duality), the supported
restriction and the evaluation, `P = K ⊠ D_X K`. As in the blueprint proof, the evaluation
kernel `K ⊠ D_X K ⟶ RΔ_* ω_X` defining the trace morphism is the adjoint of the evaluation, so
both sides are adjoint to the composite `Rc^! P ⟶ Rc^! RΔ_* LΔ^* P ⟶ Rc^! RΔ_* ω_X`, and base
change in the fixed square is natural. -/
theorem traceClass_eq_supportedRestriction :
    c.traceClass F =
      (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ F.ι)).hom ≫
        (boundedConstructibleUpperStar _ ℓ F.ι).map (c.mate ≫ c.verdierDualityIso.hom) ≫
        F.supportedRestriction _ ≫ F.supportedEvaluation := by
  unfold traceClass traceMap evaluationKernel FixedLocus.supportedEvaluation
    FixedLocus.supportedRestriction
  refine congrArg (_ ≫ ·) ?_
  exact Adjunction.homEquiv_symm_comp_map_homEquiv _ _ F.upperShriekLowerStarIso _ _ _ _


variable {B : Over (Spec (.of k))} [QuasiCompact B.hom]

/-- **The restricted trace class through the supported restriction**: the restriction of the
trace class to an open subscheme `j : B ⟶ Fix(c)` is the composite
```
ℚ̄_ℓ,B ≅ Lj^* Lι^* ℚ̄_ℓ,C --Lj^* Lι^* [u]--> Lj^* Lι^* Rc^! P --Lj^* ρ_P--> Lj^* Rd^! LΔ^* P
  --Lj^* ev--> Lj^* ω_Fix(c) ≅ Rj^! ω_Fix(c) ≅ ω_B,
```
`P = K ⊠ D_X K`, of the restrictions to `B` of the supported class, the supported restriction
and the evaluation. -/
theorem restrict_traceClass_eq_supportedRestriction [LocallyOfFiniteType B.hom] [IsSeparated B.hom]
    (j : B ⟶ F.F) [IsOpenImmersion j.left] :
    (c.traceClass F).restrict j =
      (Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ j)).hom ≫
        (boundedConstructibleUpperStar _ ℓ j).map
          ((Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ F.ι)).hom ≫
            (boundedConstructibleUpperStar _ ℓ F.ι).map (c.mate ≫ c.verdierDualityIso.hom)) ≫
        (boundedConstructibleUpperStar _ ℓ j).map (F.supportedRestriction _) ≫
        (boundedConstructibleUpperStar _ ℓ j).map F.supportedEvaluation ≫
        (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j).inv.app _ ≫
        (dualizingComplexComp ℓ j).hom := by
  rw [BorelMooreSection.restrict, traceClass_eq_supportedRestriction,
    boundedConstructibleUpperShriekUnitIso_padicAlgCl, Iso.trans_inv, Iso.symm_inv]
  exact Iso.inv_app_comp_map_comp (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j)
    _ _ _ _ _ _


/-- **The local term through the supported restriction** (blueprint
`lemma-local-term-restriction-map--1`, `lemma-local-term-restriction-map`): for an open and
closed subscheme `j : B ⟶ Fix(c)` proper over `s`, the local term `LT_B(u)` is the integral over
`B` of the composite of the restrictions to `B` of the supported class `[u]`, the supported
restriction `ρ_P` and the evaluation `ev : Rd^! LΔ^* P ⟶ ω_Fix(c)`, `P = K ⊠ D_X K`. When `B` is
a reduced fixed point `y`, the restrictions to `B` are stalks at `y`: `ρ_P` restricts to the
supported restriction `RΓ_c(T, P) ⟶ RΓ_y(X, LΔ^* P)` on the strict localization `T` of `X × X`
at `(y, y)`, and the integral over `B ≅ s` is the identification `RΓ_y(X, ω_X) ≅ RΓ(y, ω_y)`
followed by `∫_y`. -/
theorem localTerm_traceClass_eq_integral_supportedRestriction [IsProper B.hom] (j : B ⟶ F.F)
    [IsOpenImmersion j.left] [IsClosedImmersion j.left] :
    (c.traceClass F).localTerm j =
      BorelMooreSection.integral
        ((Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ j)).hom ≫
          (boundedConstructibleUpperStar _ ℓ j).map
            ((Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ F.ι)).hom ≫
              (boundedConstructibleUpperStar _ ℓ F.ι).map (c.mate ≫ c.verdierDualityIso.hom)) ≫
          (boundedConstructibleUpperStar _ ℓ j).map (F.supportedRestriction _) ≫
          (boundedConstructibleUpperStar _ ℓ j).map F.supportedEvaluation ≫
          (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ j).inv.app _ ≫
          (dualizingComplexComp ℓ j).hom) :=
  congrArg BorelMooreSection.integral (restrict_traceClass_eq_supportedRestriction c F j)

/-- **Vanishing of the local term through the supported restriction** (blueprint
`lemma-vanishing-local-term-zero-stalk--2`, proof): if the supported restriction `ρ_P`,
`P = K ⊠ D_X K`, vanishes on the open and closed subscheme `j : B ⟶ Fix(c)` proper over `s`, then
the local term `LT_B(u)` is zero. -/
theorem localTerm_traceClass_eq_zero_of_supportedRestriction [IsProper B.hom] (j : B ⟶ F.F)
    [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (h : (boundedConstructibleUpperStar _ ℓ j).map
      (F.supportedRestriction (externalProduct ℓ K (verdierDual ℓ K))) = 0) :
    (c.traceClass F).localTerm j = 0 := by
  rw [localTerm_traceClass_eq_integral_supportedRestriction, h, Limits.zero_comp,
    Limits.comp_zero, Limits.comp_zero, BorelMooreSection.integral_zero]

/-- **The local term at a fixed point through the supported restriction** (blueprint
`lemma-local-term-restriction-map--1`, `lemma-local-term-restriction-map`): let
`y : s ⟶ Fix(c)` be a fixed point that is open and closed in the fixed locus. Then the local
term `LT_y(u)` is the composite in `End(ℚ̄_ℓ,s)`
```
ℚ̄_ℓ,s ≅ (ℚ̄_ℓ,C)_y --[u]_y--> (Rc^! P)_y --(ρ_P)_y--> (Rd^! LΔ^* P)_y --ev_y--> (ω_Fix(c))_y
  ≅ Ry^! ω_Fix(c) ≅ ω_s ≅ ℚ̄_ℓ,s
```
of the stalks at `y` of the supported class, the supported restriction and the evaluation,
`P = K ⊠ D_X K`. Here `(Rc^! P)_y = RΓ_a(T, P)` and `(Rd^! LΔ^* P)_y = RΓ_y(X, LΔ^* P)`, for the
strict localization `T` of `X × X` at `(y, y)`, and the last isomorphisms are
`RΓ_y(X, ω_X) ≅ RΓ(y, ω_y)` followed by `∫_y`. -/
theorem localTerm_point_traceClass_eq_supportedRestriction (y : point k ⟶ F.F)
    [IsOpenImmersion y.left] [IsClosedImmersion y.left] :
    (c.traceClass F).localTerm y =
      .of ((Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ y)).hom ≫
        (boundedConstructibleUpperStar _ ℓ y).map
          ((Functor.Monoidal.εIso (boundedConstructibleUpperStar _ ℓ F.ι)).hom ≫
            (boundedConstructibleUpperStar _ ℓ F.ι).map (c.mate ≫ c.verdierDualityIso.hom)) ≫
        (boundedConstructibleUpperStar _ ℓ y).map (F.supportedRestriction _) ≫
        (boundedConstructibleUpperStar _ ℓ y).map F.supportedEvaluation ≫
        (boundedConstructibleUpperShriekIsoUpperStar_padicAlgCl ℓ y).inv.app _ ≫
        (dualizingComplexComp ℓ y).hom ≫ (dualizingComplexPointIso ℓ k).hom) := by
  rw [BorelMooreSection.localTerm_point, restrict_traceClass_eq_supportedRestriction]
  simp only [Category.assoc]

/-- A morphism of `Dᵇc(F)` whose pullback along `e⁻¹ ≫ j` vanishes, for an isomorphism
`e : B ≅ B'`, has vanishing pullback along `j`. -/
lemma upperStar_map_eq_zero_of_inv_comp [LocallyOfFiniteType B.hom] [IsSeparated B.hom]
    {F' B' : Over (Spec (.of k))}
    [LocallyOfFiniteType F'.hom] [QuasiCompact F'.hom] [IsSeparated F'.hom]
    [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom] (e : B ≅ B')
    (j : B ⟶ F') {M N : Dᵇc(F'.left)⟦Profinite.padicAlgClRingObj ℓ⟧} {f : M ⟶ N}
    (h : (boundedConstructibleUpperStar _ ℓ (e.inv ≫ j)).map f = 0) :
    (boundedConstructibleUpperStar _ ℓ j).map f = 0 := by
  have h₁ : (boundedConstructibleUpperStar _ ℓ e.inv).map
      ((boundedConstructibleUpperStar _ ℓ j).map f) = 0 :=
    NatIso.map_eq_zero_of_map_eq_zero (boundedConstructibleUpperStarComp _ ℓ e.inv j) h
  have h₂ : (boundedConstructibleUpperStar _ ℓ (e.hom ≫ e.inv)).map
      ((boundedConstructibleUpperStar _ ℓ j).map f) = 0 := by
    refine NatIso.map_eq_zero_of_map_eq_zero
      (boundedConstructibleUpperStarComp _ ℓ e.hom e.inv).symm ?_
    change (boundedConstructibleUpperStar _ ℓ e.hom).map
      ((boundedConstructibleUpperStar _ ℓ e.inv).map _) = 0
    rw [h₁, Functor.map_zero]
  rw [e.hom_inv_id] at h₂
  exact NatIso.map_eq_zero_of_map_eq_zero (boundedConstructibleUpperStarId _ ℓ B) h₂

end Correspondence

end AlgebraicGeometry.ProEtale.CondensedRing
