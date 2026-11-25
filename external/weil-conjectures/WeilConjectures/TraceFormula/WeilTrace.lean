/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Ring.NegOnePow
public import WeilConjectures.Algebra.Homology.DerivedCategory.SingleHomology
public import WeilConjectures.TraceFormula.FrobeniusIterate
public import WeilConjectures.TraceFormula.HomologyUnit
public import WeilConjectures.WeilObject.BoundedConstructible.LowerUpperShriek
public import WeilConjectures.WeilObject.Sheaf.StalkUnit

/-!

# Local and global Frobenius traces of Weil objects

Let `ℓ` be a prime, `k = 𝔽_q` a finite field of characteristic `p ≠ ℓ` with algebraic closure
`k̄`, `σ` the Frobenius of `Spec k̄` over `Spec k` (`geometricFrobeniusField k`) and
`s : Spec k̄ ⟶ Spec k` the geometric point of the base (`specAlgebraicClosure k`). Let `X` be a
separated scheme of finite type over `Spec k` with an automorphism `e : X ≅ X` over `Spec k`, and
let `(K, φ_K)` be a Weil object of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` for `e`
(`ProEtale.CondensedRing.WeilBoundedConstructible`). This file defines the two sides of the
Grothendieck–Lefschetz trace formula from the existing Weil functors only: the Weil homology
sheaves (`WeilBoundedConstructible.homologyFunctor`), the Weil stalks
(`WeilSheaf.stalkFunctor`) and the Weil lower shriek (`weilLowerShriek`). No Frobenius
correspondence is introduced.

## Rational points

All Frobenius powers are indexed by `n : ℕ`, with `e⁰ = 𝟙` (`CategoryTheory.Iso.pow`). The points
of degree `n` (`ProEtale.CondensedRing.frobeniusFixedPoints e n`) are the geometric points
`x̄ : Spec k̄ ⟶ X` over `s` with `x̄ ≫ eⁿ = σⁿ ≫ x̄`. For `e = 𝟙` and `n ≠ 0` these are the
`k̄`-points of `X` with coordinates in the fixed field `𝔽_{qⁿ}` of `σⁿ`, that is the
`𝔽_{qⁿ}`-rational points of `X`; for a general `e` they are the fixed points of the Frobenius `σⁿ`
twisted by `eⁿ`. Each rational point is counted once: the geometric point is the rational point
itself, not a chosen geometric lift, so no independence of the lift is needed.

## The traces

All stalks live in the symmetric monoidal category `Mod_{Spec k̄}` of `ℚ̲̄_ℓ`-modules on the
pro-étale site of `Spec k̄` (`ProEtale.CondensedRing.GeometricPointMod`), and traces take values
in the ring `End (𝟙_ Mod_{Spec k̄})`, the categorical traces of
`WeilConjectures.TraceFormula.CategoricalTrace`. Through the equivalence of `Mod_{Spec k̄}` with
condensed `ℚ̲̄_ℓ`-modules (`isEquivalence_upperStarFromPointMod`) this ring is
`End(ℚ̲̄_ℓ) = ℚ̄_ℓ`, and the categorical trace of an endomorphism of a finite-dimensional
`ℚ̄_ℓ`-vector space is its usual trace.

* **Local trace.** For a Weil sheaf `F` and a point `x̄` of degree `n`, the stalk of the Weil
  sheaf `(F, φ_F^{(n)})` for `eⁿ` at `x̄` (`WeilSheaf.frobeniusStalk`) is `F_x̄` with its `n`-th
  Frobenius operator `Fr_{x̄,n}`. For a Weil complex `K`,
  ```
  tₙ(K; x̄) = ∑ⱼ (-1)ʲ Tr(Fr_{x̄,n} | Hʲ(K)_x̄)
  ```
  is `weilStalkTraceAlternatingSum`, the alternating sum of the traces on the stalks of the Weil
  homology sheaves. Since the stalk functor is exact, `Hʲ(K)_x̄ = Hʲ(K_x̄)`.
* **Global trace.** The compactly supported cohomology `RΓ_c(X, K) = Ra_! K` of a Weil object is
  the Weil object `Ra_!^Weil K` on the base `Spec k` (`ProEtale.CondensedRing.point k`) with the
  identity automorphism (`weilCompactSupportCohomology`), for `a : X ⟶ Spec k` the structure
  morphism (`toPoint X`). Its stalk at
  `s`, with the `n`-th Frobenius operator, is `RΓ_c(X_k̄, K)` with `Fr_{c,n}`, and
  ```
  Lₙ(X, K) = ∑ᵢ (-1)ⁱ Tr(Fr_{c,n} | Hⁱ_c(X_k̄, K))
  ```
  is the local trace of `Ra_!^Weil K` at the unique point `s` of the base
  (`weilStalkTraceAlternatingSum` at `specAlgebraicClosure k`), so the absolute trace formula is
  a special case of the relative one.

## Main definitions

- `ProEtale.CondensedRing.frobeniusFixedPoints`: the points of degree `n`.
- `ProEtale.CondensedRing.WeilSheaf.powStalkFunctor`: the stalk at a point of degree `n` with
  its `n`-th Frobenius operator, as a functor.
- `ProEtale.CondensedRing.weilSheafStalkTrace`: the trace of the `n`-th Frobenius on a stalk of
  a Weil sheaf.
- `ProEtale.CondensedRing.weilStalkTraceAlternatingSum`: the local trace `tₙ(K; x̄)`.
- `ProEtale.CondensedRing.weilCompactSupportCohomology`: `RΓ_c(X, K)` as a Weil object.
- `ProEtale.CondensedRing.weilUnit`: the unit `ℚ̲̄_ℓ,X` with its canonical Weil structure, that is
  `ProEtale.CondensedRing.WeilBoundedConstructible.unit` for `e`.

The base `Spec k` is `ProEtale.CondensedRing.point k`, from
`WeilConjectures.TraceFormula.Basic`.

## Main results

- `ProEtale.CondensedRing.weilSheafStalkTrace_congr`,
  `ProEtale.CondensedRing.categoricalTrace_frobeniusStalk_congr`: the local trace only depends on
  the Weil sheaf up to isomorphism.
- `ProEtale.CondensedRing.finite_support_weilSheafStalkTrace_homology`: only finitely many
  homology sheaves of a bounded complex contribute to the local trace.
- `ProEtale.CondensedRing.weilSheafStalkTrace_unit`: the unit Weil sheaf has trace `1` at every
  point of degree `n ≠ 0`.
- `ProEtale.CondensedRing.weilStalkTraceAlternatingSum_weilUnit`: the canonical Weil unit has
  local trace `1` at every point of degree `n ≠ 0`, the normalization test N1.

The points of degree `n ≠ 0` are finite
(`ProEtale.CondensedRing.finite_frobeniusFixedPoints`, in
`WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite`).

## Implementation notes

The `(n + 1)`-st iterated Weil structure of the unit is computed with `Iso.powSuccStr`
(`WeilSheaf.pow_succ`), which does not involve the identity isomorphism `𝟙^* ≅ 𝟭` of the
pullback; the unit results are stated for `n ≠ 0`.

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Endofunctor

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The category `Mod_{Spec Ω}` of `ℚ̲̄_ℓ`-modules on the pro-étale site of `Spec Ω`, in which the
stalks of Weil sheaves at geometric points with values in `Ω` live. -/
abbrev GeometricPointMod (Ω : Type u) [Field Ω] : Type _ :=
  CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology (Spec (.of Ω))) Ab.{u + 1})
    (condensedRingObj (Profinite.padicAlgClRingObj ℓ) (Spec (.of Ω)))

variable {k : Type u} [Field k]

/-! ### Rational points -/

section Points

variable [Finite k] {X : Over (Spec (.of k))} (e : X ≅ X) (n : ℕ)

/-- The points of degree `n` of `X` for the Frobenius twisted by `e`: the geometric points
`x̄ : Spec k̄ ⟶ X` over the geometric point `s : Spec k̄ ⟶ Spec k` of the base with
`x̄ ≫ eⁿ = σⁿ ≫ x̄`. For `e = 𝟙` and `n ≠ 0` these are the `𝔽_{qⁿ}`-rational points of `X`. -/
def frobeniusFixedPoints : Type u :=
  {x : Spec (.of (AlgebraicClosure k)) ⟶ X.left //
    x ≫ X.hom = specAlgebraicClosure k ∧
      x ≫ (e.pow n).hom.left = ((geometricFrobeniusField k).pow n).hom ≫ x}

end Points

/-! ### The local trace -/

/-- The trace of the structure automorphism of an algebra for the identity functor only depends
on the algebra up to isomorphism. -/
lemma _root_.CategoryTheory.Endofunctor.IsoAlgebra.categoricalTrace_str_congr {C : Type*}
    [Category C] [MonoidalCategory C] [BraidedCategory C] {A B : IsoAlgebra (𝟭 C)} (i : A ≅ B)
    [HasRightDual A.carrier] [HasRightDual B.carrier] :
    categoricalTrace (V := B.carrier) B.str.hom = categoricalTrace (V := A.carrier) A.str.hom := by
  let e : A.carrier ≅ B.carrier := (IsoAlgebra.forget _).mapIso i
  have h : B.str.hom = e.inv ≫ A.str.hom ≫ e.hom := (Iso.eq_inv_comp e).2 i.hom.hom.h
  exact (congrArg (categoricalTrace (V := B.carrier)) h).trans (categoricalTrace_conj e _)

/-- `traceOrZero` of the structure automorphism of an algebra for the identity functor only depends
on the algebra up to isomorphism. -/
lemma _root_.CategoryTheory.Endofunctor.IsoAlgebra.traceOrZero_str_congr {C : Type*}
    [Category C] [MonoidalCategory C] [BraidedCategory C] [Preadditive C]
    {A B : IsoAlgebra (𝟭 C)} (i : A ≅ B) :
    traceOrZero B.str.hom = traceOrZero A.str.hom := by
  let e : A.carrier ≅ B.carrier := (IsoAlgebra.forget _).mapIso i
  have h : B.str.hom = e.inv ≫ A.str.hom ≫ e.hom := (Iso.eq_inv_comp e).2 i.hom.hom.h
  exact (congrArg traceOrZero h).trans (traceOrZero_conj e _)

/-- If the carrier of an algebra for the identity functor is isomorphic to the unit, by an
isomorphism conjugating the structure automorphism to the identity, then the structure
automorphism has trace `1`. -/
lemma _root_.CategoryTheory.Endofunctor.IsoAlgebra.traceOrZero_str_hom_eq_one {C : Type*}
    [Category C] [MonoidalCategory C] [BraidedCategory C] [Preadditive C] (A : IsoAlgebra (𝟭 C))
    (ε : 𝟙_ C ≅ A.carrier) (h : ε.hom ≫ A.str.hom ≫ ε.inv = 𝟙 _) :
    traceOrZero A.str.hom = 1 := by
  rw [← traceOrZero_conj ε.symm, Iso.symm_inv, Iso.symm_hom, h]
  exact traceOrZero_id_tensorUnit

section Local

variable [Finite k] {X : Over (Spec (.of k))} {e : X ≅ X} (n : ℕ)
  (x : Spec (.of (AlgebraicClosure k)) ⟶ X.left)
  (hx : x ≫ (e.pow n).hom.left = ((geometricFrobeniusField k).pow n).hom ≫ x)

/-- The stalk at a geometric point `x̄` with `x̄ ≫ eⁿ = σⁿ ≫ x̄` of Weil sheaves for `e`, with the
`n`-th Frobenius operator: the stalk functor for `eⁿ` after `WeilSheaf.powFunctor`. -/
noncomputable def WeilSheaf.powStalkFunctor :
    WeilSheaf ℓ e ⥤ IsoAlgebra (𝟭 (GeometricPointMod ℓ (AlgebraicClosure k))) :=
  WeilSheaf.powFunctor ℓ e n ⋙
    WeilSheaf.stalkFunctor ℓ (e.pow n) ((geometricFrobeniusField k).pow n).hom x hx

/-- The stalk at a geometric point `x̄` with `x̄ ≫ eⁿ = σⁿ ≫ x̄` of a Weil sheaf `F` for `e`, with
its `n`-th Frobenius operator: the stalk of the Weil sheaf `(F, φ_F^{(n)})` for `eⁿ`. -/
noncomputable def WeilSheaf.frobeniusStalk (F : WeilSheaf ℓ e) :
    IsoAlgebra (𝟭 (GeometricPointMod ℓ (AlgebraicClosure k))) :=
  (WeilSheaf.powStalkFunctor ℓ n x hx).obj F

/-- The trace of the Frobenius on the stalk only depends on the Weil sheaf up to isomorphism. -/
lemma categoricalTrace_frobeniusStalk_congr {F G : WeilSheaf ℓ e} (i : F ≅ G)
    [HasRightDual (WeilSheaf.frobeniusStalk ℓ n x hx F).carrier]
    [HasRightDual (WeilSheaf.frobeniusStalk ℓ n x hx G).carrier] :
    categoricalTrace (V := (WeilSheaf.frobeniusStalk ℓ n x hx F).carrier)
        (WeilSheaf.frobeniusStalk ℓ n x hx F).str.hom =
      categoricalTrace (V := (WeilSheaf.frobeniusStalk ℓ n x hx G).carrier)
        (WeilSheaf.frobeniusStalk ℓ n x hx G).str.hom :=
  (IsoAlgebra.categoricalTrace_str_congr (A := WeilSheaf.frobeniusStalk ℓ n x hx F)
    (B := WeilSheaf.frobeniusStalk ℓ n x hx G) ((WeilSheaf.powStalkFunctor ℓ n x hx).mapIso i)).symm

/-- The trace `Tr(Fr_{x̄,n} | F_x̄)` of the `n`-th Frobenius operator on the stalk of a Weil sheaf
at a geometric point `x̄` with `x̄ ≫ eⁿ = σⁿ ≫ x̄`: the categorical trace computed with a right
dual chosen from `Nonempty (HasRightDual F_x̄)` (`traceOrZero`, `weilSheafStalkTrace_eq`),
and `0` when the stalk has no right dual. The stalks of constructible sheaves are
finite-dimensional over `ℚ̄_ℓ`, hence dualizable, so the second case does not occur for the
homology sheaves of the trace formula. -/
noncomputable def weilSheafStalkTrace (F : WeilSheaf ℓ e) :
    End (𝟙_ (GeometricPointMod ℓ (AlgebraicClosure k))) :=
  traceOrZero (WeilSheaf.frobeniusStalk ℓ n x hx F).str.hom

/-- For any right dual of the stalk, `weilSheafStalkTrace` is the categorical trace computed with
that dual. -/
lemma weilSheafStalkTrace_eq (F : WeilSheaf ℓ e)
    [d : HasRightDual (WeilSheaf.frobeniusStalk ℓ n x hx F).carrier] :
    weilSheafStalkTrace ℓ n x hx F =
      categoricalTrace (V := (WeilSheaf.frobeniusStalk ℓ n x hx F).carrier)
        (WeilSheaf.frobeniusStalk ℓ n x hx F).str.hom :=
  @traceOrZero_eq_categoricalTrace _ _ _ _ _ _ d _

/-- The trace of the Frobenius on the stalk only depends on the Weil sheaf up to isomorphism. -/
lemma weilSheafStalkTrace_congr {F G : WeilSheaf ℓ e} (i : F ≅ G) :
    weilSheafStalkTrace ℓ n x hx F = weilSheafStalkTrace ℓ n x hx G :=
  (IsoAlgebra.traceOrZero_str_congr ((WeilSheaf.powStalkFunctor ℓ n x hx).mapIso i)).symm

variable [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

/-- The local trace `tₙ(K; x̄) = ∑ⱼ (-1)ʲ Tr(Fr_{x̄,n} | Hʲ(K)_x̄)` of a Weil object `K` of
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧` at a geometric point `x̄` with `x̄ ≫ eⁿ = σⁿ ≫ x̄`: the alternating sum of the
traces of the `n`-th Frobenius on the stalks of the Weil homology sheaves. -/
noncomputable def weilStalkTraceAlternatingSum (K : WeilBoundedConstructible ℓ e.hom) :
    End (𝟙_ (GeometricPointMod ℓ (AlgebraicClosure k))) :=
  ∑ᶠ j : ℤ, (j.negOnePow : ℤ) •
    weilSheafStalkTrace ℓ n x hx ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj K)

/-- Only finitely many homology sheaves of a bounded complex contribute to the local trace, so
that the `finsum` defining it is a finite sum. -/
theorem finite_support_weilSheafStalkTrace_homology (K : WeilBoundedConstructible ℓ e.hom) :
    (Function.support fun j : ℤ ↦
      weilSheafStalkTrace ℓ n x hx
        ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj K)).Finite := by
  obtain ⟨⟨a, b, h⟩, -⟩ := (mem_boundedConstructible_iff _ _).1 K.carrier.property
  refine (Set.finite_Icc a b).subset fun j hj ↦ ?_
  by_contra hj'
  have hZ : Limits.IsZero (WeilSheaf.frobeniusStalk ℓ n x hx
      ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj K)).carrier := by
    rw [WeilSheaf.frobeniusStalk, WeilSheaf.powStalkFunctor, Functor.comp_obj,
      WeilSheaf.stalkFunctor_obj_carrier, WeilSheaf.powFunctor_obj,
      WeilSheaf.pow_carrier,
      WeilBoundedConstructible.homologyFunctor_obj_carrier]
    refine Functor.map_isZero _ (h j ?_)
    simpa only [Set.mem_Icc, not_and_or, not_le] using hj'
  refine hj ?_
  exact traceOrZero_eq_zero_of_isZero hZ _

end Local

/-! ### The unit Weil sheaf -/

/-- Let `P g` be a family of endofunctors indexed by the endomorphisms `g` of `X`, contravariant
up to the composition isomorphisms `comp`, and let `ε g : a ≅ P g a` be isomorphisms compatible
with `comp`. Then the iterated structure isomorphisms of `(ε e)⁻¹` are the inverses of the
`ε (e^{n+1})`. -/
theorem _root_.CategoryTheory.Iso.powSuccStr_symm_hom_eq_inv {C D : Type*} [Category C]
    [Category D] {X : C} (e : X ≅ X) (P : (X ⟶ X) → D ⥤ D)
    (comp : ∀ f g : X ⟶ X, P (f ≫ g) ≅ P g ⋙ P f) {a : D} (ε : ∀ g : X ⟶ X, a ≅ (P g).obj a)
    (h : ∀ f g : X ⟶ X, (comp f g).hom.app a ≫ (P f).map (ε g).inv ≫ (ε f).inv = (ε (f ≫ g)).inv)
    (n : ℕ) : (e.powSuccStr P comp (ε e.hom).symm n).hom = (ε (e.pow (n + 1)).hom).inv := by
  induction n with
  | zero =>
    have key : ∀ (g g' : X ⟶ X) (h : g = g'),
        eqToHom (congrArg (fun g ↦ (P g).obj a) h) ≫ (ε g').inv = (ε g).inv := by
      rintro g _ rfl
      simp
    exact key _ _ (Category.id_comp e.hom)
  | succ n ih =>
    simp only [Iso.powSuccStr, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom, ih]
    exact h _ _

/-- An abstract form of the Frobenius of the stalk of a unit object: let `τ : σ^* ≅ 𝟭`,
`c₁ : y^* ≅ x^* ⋙ σ^*`, `y^* = z^*` and `c₂ : z^* ≅ e^* ⋙ x^*` be compatible with unit
comparisons `ε`. Then the composite `x^* a ≅ σ^* x^* a ≅ y^* a = z^* a ≅ x^* e^* a ≅ x^* a`,
conjugated by `εₓ`, is `τ⁻¹ ≫ ε_σ⁻¹`. -/
theorem _root_.CategoryTheory.Iso.hom_comp_whiskerLeft_comp_inv_eq {A B : Type*} [Category A]
    [Category B] {xs : A ⥤ B} {es : A ⥤ A} {ss : B ⥤ B} {ys zs : A ⥤ B} (τ : ss ≅ 𝟭 B)
    (c₁ : ys ≅ xs ⋙ ss) (hyz : ys = zs) (c₂ : zs ≅ es ⋙ xs) {a : A} {b : B}
    (εx : b ≅ xs.obj a) (φ : es.obj a ≅ a) (εs : b ≅ ss.obj b) (εz : b ≅ zs.obj a)
    (h₂ : c₂.hom.app a ≫ xs.map φ.hom ≫ εx.inv = εz.inv)
    (h₁ : c₁.hom.app a ≫ ss.map εx.inv ≫ εs.inv =
      eqToHom (congrArg (fun F ↦ F.obj a) hyz) ≫ εz.inv) :
    εx.hom ≫ ((Functor.isoWhiskerLeft xs τ.symm ≪≫ c₁.symm ≪≫ eqToIso hyz ≪≫ c₂).app a ≪≫
      xs.mapIso φ).hom ≫ εx.inv = τ.inv.app b ≫ εs.inv := by
  simp only [Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Iso.symm_hom, eqToIso.hom, eqToHom_app, Functor.mapIso_hom,
    Category.assoc, h₂]
  rw [← h₁, Iso.inv_hom_id_app_assoc, ← Functor.id_map εx.hom, τ.inv.naturality_assoc,
    ← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The composition isomorphism of pullbacks of module objects, transported along an equality
`f ≫ g = t`, is compatible with the unit comparisons. -/
lemma upperStarComp_hom_app_unit_of_eq (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {t : X ⟶ Z}
    (ht : f ≫ g = t) (c : (t)^*⟦Λ⟧ ≅ (g)^*⟦Λ⟧ ⋙ (f)^*⟦Λ⟧)
    (hc : c = eqToIso (congrArg (upperStar Λ) ht.symm) ≪≫ upperStarComp Λ f g) :
    c.hom.app (𝟙_ _) ≫ (f)^*⟦Λ⟧.map (Functor.Monoidal.εIso (g)^*⟦Λ⟧).inv ≫
      (Functor.Monoidal.εIso (f)^*⟦Λ⟧).inv = (Functor.Monoidal.εIso (t)^*⟦Λ⟧).inv := by
  subst ht hc
  rw [eqToIso_refl, Iso.refl_trans, upperStarComp_hom_app_unit]

/-- The unit comparisons of the pullbacks of module objects along equal morphisms agree up to
the cast. -/
lemma eqToHom_comp_upperStar_εIso_inv {Y Z : Scheme.{u}} {f f' : Y ⟶ Z} (hf : f = f')
    (h : (f)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj (𝟙_ _) =
      (f')^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj (𝟙_ _)) :
    eqToHom h ≫ (Functor.Monoidal.εIso (f')^*⟦Profinite.padicAlgClRingObj ℓ⟧).inv =
      (Functor.Monoidal.εIso (f)^*⟦Profinite.padicAlgClRingObj ℓ⟧).inv := by
  subst hf
  rw [eqToHom_refl, Category.id_comp]

section UnitSheaf

variable {X : Over (Spec (.of k))} (e : X ≅ X)

/-- The unit Weil sheaf `ℚ̲̄_ℓ,X` for `e`: the unit module object with the structure isomorphism
`e^* ℚ̲̄_ℓ,X ≅ ℚ̲̄_ℓ,X` of the monoidal functor `e^*`. -/
noncomputable def WeilSheaf.unit : WeilSheaf ℓ e :=
  IsoAlgebra.mk (𝟙_ _) (Functor.Monoidal.εIso (e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).symm

lemma WeilSheaf.unit_str :
    (WeilSheaf.unit ℓ e).str =
      (Functor.Monoidal.εIso (e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).symm :=
  IsoAlgebra.mk_str _ _

/-- The composition isomorphism `(f.left ≫ g.left)^* ≅ g.left^* ⋙ f.left^*`, seen as an
isomorphism out of `((f ≫ g).left)^*`, is its transport along `(f ≫ g).left = f.left ≫ g.left`.
Stating it propositionally keeps the kernel from unfolding the pullbacks. -/
lemma upperStarComp_left_eq (f g : X ⟶ X) :
    (upperStarComp (Profinite.padicAlgClRingObj ℓ) f.left g.left :
      ((f ≫ g).left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅ _) =
    eqToIso (congrArg (upperStar (Profinite.padicAlgClRingObj ℓ)) (Over.comp_left _ _ _ f g)) ≪≫
      upperStarComp (Profinite.padicAlgClRingObj ℓ) f.left g.left := by
  rw [eqToIso_refl, Iso.refl_trans]

/-- The iterated structure isomorphisms of the unit Weil sheaf are the inverses of the unit
comparisons of the pullbacks `(e^{n+1})^*`. -/
lemma powSuccStr_εIso_symm_hom (n : ℕ) :
    (e.powSuccStr (fun g ↦ (g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
      (fun f g ↦ upperStarComp (Profinite.padicAlgClRingObj ℓ) f.left g.left)
      (Functor.Monoidal.εIso (e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).symm n).hom =
      (Functor.Monoidal.εIso ((e.pow (n + 1)).hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).inv :=
  e.powSuccStr_symm_hom_eq_inv _ _
    (fun g ↦ Functor.Monoidal.εIso (g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
    (fun f g ↦ upperStarComp_hom_app_unit_of_eq _ f.left g.left (Over.comp_left _ _ _ f g).symm
      _ (upperStarComp_left_eq ℓ f g)) n

/-- The unit Weil sheaf for `e`, as a Weil sheaf for `e^{n+1}`, is the unit Weil sheaf for
`e^{n+1}`. -/
lemma WeilSheaf.pow_unit (n : ℕ) :
    WeilSheaf.pow ℓ (WeilSheaf.unit ℓ e) (n + 1) = WeilSheaf.unit ℓ (e.pow (n + 1)) := by
  rw [WeilSheaf.pow_succ, WeilSheaf.unit_str]
  unfold WeilSheaf.unit
  congr 1
  ext1
  rw [Iso.symm_hom]
  exact powSuccStr_εIso_symm_hom ℓ e n

/-- The Frobenius on the stalk of the unit Weil sheaf, conjugated by the unit comparison
`ε_x : Λ ≅ x̄^* Λ`, is the identity: by `Iso.hom_comp_whiskerLeft_comp_inv_eq` it is
`τ⁻¹ ≫ ε_σ⁻¹` at the unit, for `τ = upperStarIsoIdOfIsSepClosed σ`, and
`τ = ε_σ⁻¹` there by `upperStarIsoIdOfIsSepClosed_hom_app_unit`. -/
lemma WeilSheaf.stalkFunctor_obj_unit_str_hom {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (σ : Spec (.of Ω) ⟶ Spec (.of Ω)) (x : Spec (.of Ω) ⟶ X.left)
    (hx : x ≫ e.hom.left = σ ≫ x) :
    (Functor.Monoidal.εIso (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧).hom ≫
      ((WeilSheaf.stalkFunctor ℓ e σ x hx).obj (WeilSheaf.unit ℓ e)).str.hom ≫
        (Functor.Monoidal.εIso (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧).inv = 𝟙 _ := by
  rw [WeilSheaf.stalkFunctor_obj_str, WeilSheaf.unit_str, weilStalkComparison,
    upperStarEqToIso_eq_eqToIso]
  have key := Iso.hom_comp_whiskerLeft_comp_inv_eq
    (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ)
    (upperStarComp (Profinite.padicAlgClRingObj ℓ) σ x)
    (congrArg (upperStar (Profinite.padicAlgClRingObj ℓ)) hx.symm)
    (upperStarComp (Profinite.padicAlgClRingObj ℓ) x e.hom.left)
    (Functor.Monoidal.εIso (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
    (Functor.Monoidal.εIso (e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧).symm
    (Functor.Monoidal.εIso (σ)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
    (Functor.Monoidal.εIso (x ≫ e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
    (upperStarComp_hom_app_unit _ x e.hom.left)
    ((upperStarComp_hom_app_unit _ σ x).trans (eqToHom_comp_upperStar_εIso_inv ℓ hx.symm _).symm)
  refine key.trans ?_
  rw [← upperStarIsoIdOfIsSepClosed_hom_app_unit, Iso.inv_hom_id_app]
  rfl

/-- The Frobenius on the stalk of the unit Weil sheaf has trace `1`: conjugated by the unit
comparison `ε_x : Λ ≅ x̄^* Λ` it is the identity (`WeilSheaf.stalkFunctor_obj_unit_str_hom`). -/
lemma WeilSheaf.traceOrZero_stalkFunctor_obj_unit_str_hom {Ω : Type u} [Field Ω]
    [hΩ : IsSepClosed Ω] (σ : Spec (.of Ω) ⟶ Spec (.of Ω)) (x : Spec (.of Ω) ⟶ X.left)
    (hx : x ≫ e.hom.left = σ ≫ x) :
    @Eq (End (𝟙_ (GeometricPointMod ℓ Ω)))
      (traceOrZero (C := GeometricPointMod ℓ Ω)
        (IsoAlgebra.str (C := GeometricPointMod ℓ Ω) (F := 𝟭 (GeometricPointMod ℓ Ω))
          (Functor.obj (D := IsoAlgebra (𝟭 (GeometricPointMod ℓ Ω)))
            (WeilSheaf.stalkFunctor ℓ e σ x hx) (WeilSheaf.unit ℓ e))).hom) 1 :=
  IsoAlgebra.traceOrZero_str_hom_eq_one _
    (Functor.Monoidal.εIso (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
    (WeilSheaf.stalkFunctor_obj_unit_str_hom ℓ e σ x hx)

end UnitSheaf

/-! ### The canonical Weil unit -/

section Unit

variable [Finite k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (e : X ≅ X)

/-- The unit `ℚ̲̄_ℓ,X` of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` with its canonical Weil structure
`Le^* ℚ̲̄_ℓ,X ≅ ℚ̲̄_ℓ,X`, the inverse of the unit isomorphism of the monoidal functor `Le^*`: the
constant Weil object `WeilBoundedConstructible.unit` for `e`. -/
noncomputable abbrev weilUnit : WeilBoundedConstructible ℓ e.hom :=
  WeilBoundedConstructible.unit ℓ e.hom

omit [Finite k] in
/-- The homology sheaves `Hʲ(ℚ̲̄_ℓ,X)` of the canonical Weil unit vanish in degrees `j ≠ 0`: the
unit of the derived category is the unit module object placed in degree `0`. -/
lemma isZero_homologyFunctor_unit_carrier {j : ℤ} (hj : j ≠ 0) :
    Limits.IsZero ((WeilBoundedConstructible.homologyFunctor ℓ e j).obj
      (WeilBoundedConstructible.unit ℓ e.hom)).carrier := by
  rw [WeilBoundedConstructible.homologyFunctor_obj_carrier]
  exact DerivedCategory.isZero_homologyFunctor_obj_of_iso_singleFunctor
    (DerivedCategory.singleFunctorObjUnitIso _).symm hj

/-- `H⁰(ℚ̲̄_ℓ,X) ≅ ℚ̲̄_ℓ,X` as Weil sheaves for `e`: the identification `H⁰(ℚ̲̄_ℓ[0]) ≅ ℚ̲̄_ℓ` is
compatible with the structure isomorphisms
(`WeilBoundedConstructible.homologyFunctor_obj_unit_str_hom_comp`). -/
noncomputable def WeilBoundedConstructible.homologyFunctorZeroUnitIso :
    (WeilBoundedConstructible.homologyFunctor ℓ e 0).obj (WeilBoundedConstructible.unit ℓ e.hom) ≅
      WeilSheaf.unit ℓ e :=
  IsoAlgebra.isoMk (DerivedCategory.homologyFunctorZeroQhSingleIso _ (𝟙_ _))
    (WeilBoundedConstructible.homologyFunctor_obj_unit_str_hom_comp ℓ e).symm

/-- The local trace of the canonical Weil unit is the trace of the Frobenius on the stalk of its
homology sheaf `H⁰(ℚ̲̄_ℓ,X)`, the other homology sheaves being zero. -/
lemma weilStalkTraceAlternatingSum_unit_eq_weilSheafStalkTrace (n : ℕ)
    (x : Spec (.of (AlgebraicClosure k)) ⟶ X.left)
    (hx : x ≫ (e.pow (n + 1)).hom.left = ((geometricFrobeniusField k).pow (n + 1)).hom ≫ x) :
    weilStalkTraceAlternatingSum ℓ (n + 1) x hx (WeilBoundedConstructible.unit ℓ e.hom) =
      weilSheafStalkTrace ℓ (n + 1) x hx ((WeilBoundedConstructible.homologyFunctor ℓ e 0).obj
        (WeilBoundedConstructible.unit ℓ e.hom)) := by
  rw [weilStalkTraceAlternatingSum]
  refine (finsum_eq_single _ 0 fun j hj ↦ ?_).trans ?_
  · refine smul_eq_zero_of_right _ (traceOrZero_eq_zero_of_isZero ?_ _)
    rw [Functor.id_obj, WeilSheaf.frobeniusStalk, WeilSheaf.powStalkFunctor, Functor.comp_obj,
      WeilSheaf.stalkFunctor_obj_carrier, WeilSheaf.powFunctor_obj, WeilSheaf.pow_carrier]
    exact Functor.map_isZero _ (isZero_homologyFunctor_unit_carrier ℓ e hj)
  · rw [Int.negOnePow_zero, Units.val_one, one_smul]

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] in
/-- The unit Weil sheaf `ℚ̲̄_ℓ,X` has trace `1` at every point: its stalk is the unit, on which the
Frobenius acts trivially. By `WeilSheaf.pow_unit` the stalk is that of the unit Weil sheaf for
`e^{n+1}`, whose Frobenius has trace `1`
(`WeilSheaf.traceOrZero_stalkFunctor_obj_unit_str_hom`). This gives
`weilStalkTraceAlternatingSum_weilUnit`, the normalization test N1. -/
lemma weilSheafStalkTrace_unit (n : ℕ) (x : Spec (.of (AlgebraicClosure k)) ⟶ X.left)
    (hx : x ≫ (e.pow (n + 1)).hom.left = ((geometricFrobeniusField k).pow (n + 1)).hom ≫ x) :
    weilSheafStalkTrace ℓ (n + 1) x hx (WeilSheaf.unit ℓ e) = 1 := by
  rw [weilSheafStalkTrace, WeilSheaf.frobeniusStalk, WeilSheaf.powStalkFunctor,
    Functor.comp_obj, WeilSheaf.powFunctor_obj, WeilSheaf.pow_unit]
  exact WeilSheaf.traceOrZero_stalkFunctor_obj_unit_str_hom ℓ _ (hΩ := _) _ x hx

/-- The canonical Weil unit has local trace `1` at every point of degree `n ≠ 0`: its stalk is
`ℚ̄_ℓ` in degree `0`, on which the Frobenius acts trivially (normalization test N1). This is the
unit stalk trace used in the proof of the twisted variant of blueprint
`corollary-point-counting-zeta-function--2`. -/
theorem weilStalkTraceAlternatingSum_weilUnit (n : ℕ) [NeZero n]
    (x : Spec (.of (AlgebraicClosure k)) ⟶ X.left)
    (hx : x ≫ (e.pow n).hom.left = ((geometricFrobeniusField k).pow n).hom ≫ x) :
    weilStalkTraceAlternatingSum ℓ n x hx (weilUnit ℓ e) = 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne n)
  rw [weilStalkTraceAlternatingSum_unit_eq_weilSheafStalkTrace,
    weilSheafStalkTrace_congr ℓ (m + 1) x hx
      (WeilBoundedConstructible.homologyFunctorZeroUnitIso ℓ e)]
  exact weilSheafStalkTrace_unit ℓ e m x hx

end Unit

/-! ### The global trace -/

section Global

variable [Finite k]

/-- The geometric point `s : Spec k̄ ⟶ Spec k` of the base is fixed by the Frobenius:
`s ≫ 𝟙 = σⁿ ≫ s`. -/
lemma specAlgebraicClosure_comp_pow (n : ℕ) :
    specAlgebraicClosure k ≫ ((Iso.refl (point k)).pow n).hom.left =
      ((geometricFrobeniusField k).pow n).hom ≫ specAlgebraicClosure k := by
  rw [Iso.pow_hom_comp_of_hom_comp _ (geometricFrobeniusField_hom_comp_specAlgebraicClosure k),
    Iso.pow_refl]
  exact Category.comp_id _

/-- The geometric point `s` of the base is its unique point of degree `n`. -/
noncomputable instance (n : ℕ) : Unique (frobeniusFixedPoints (Iso.refl (point k)) n) where
  default := ⟨specAlgebraicClosure k, Category.comp_id _, specAlgebraicClosure_comp_pow n⟩
  uniq x := Subtype.ext ((Category.comp_id _).symm.trans x.2.1)

variable [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (e : X ≅ X)

/-- The compactly supported cohomology `RΓ_c(X, K) = Ra_! K` of a Weil object `K` for `e`, as a
Weil object on the base `Spec k` for the identity: the Weil lower shriek along the structure
morphism `a` (`toPoint X`). -/
noncomputable def weilCompactSupportCohomology :
    WeilBoundedConstructible ℓ e.hom ⥤ WeilBoundedConstructible ℓ (Iso.refl (point k)).hom :=
  weilLowerShriek ℓ e (Iso.refl (point k)) (f := toPoint X) (toPoint_ext _ _)

end Global

end AlgebraicGeometry.ProEtale.CondensedRing
