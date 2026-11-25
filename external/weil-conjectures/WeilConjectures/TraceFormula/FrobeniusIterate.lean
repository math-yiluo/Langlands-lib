/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.WeilObject.Sheaf.Stalk

/-!

# The iterated Frobenius operators of a Weil sheaf

Let `e : X ≅ X` be an automorphism. The trace formula for the `n`-th Frobenius, `n : ℕ`, uses the
power `eⁿ` of `e` (`CategoryTheory.Iso.pow e n`), defined like the power in a monoid by `e⁰ = 𝟙`
and `e^{n+1} = eⁿ ≫ e`. For a Weil sheaf `(F, φ_F)` of `ℚ̄_ℓ`-modules for `e`, the `n`-fold iterate
of its structure isomorphism makes `F` a Weil sheaf for `eⁿ`
(`ProEtale.CondensedRing.WeilSheaf.pow`):
```
φ_F^{(0)} : 𝟙^* F ≅ F,
φ_F^{(n+1)} : (eⁿ ≫ e)^* F ≅ (eⁿ)^* e^* F --(eⁿ)^* φ_F--> (eⁿ)^* F --φ_F^{(n)}--> F,
```
the first isomorphism being the identity isomorphism `ProEtale.CondensedRing.upperStarId` and the
second the composition isomorphism `ProEtale.CondensedRing.upperStarComp` of pullbacks on module
objects.

The stalk at a geometric point `x̄` with `x̄ ≫ eⁿ = σⁿ ≫ x̄` of the Weil sheaf `(F, φ_F^{(n)})` for
`eⁿ` (`ProEtale.CondensedRing.WeilSheaf.stalkFunctor`) is the stalk of `F` with its `n`-th
Frobenius operator. For `x̄` the geometric point over an `𝔽_{qⁿ}`-rational point this is the
action of the Frobenius of `𝔽_{qⁿ}` on the stalk.

## Main definitions

- `CategoryTheory.Iso.pow`: the power `eⁿ` of an automorphism.
- `CategoryTheory.Iso.powStr`: the iterated structure isomorphism `(P eⁿ) a ≅ a` for a family of
  endofunctors `P` contravariant in endomorphisms up to identity and composition isomorphisms.
- `CategoryTheory.Iso.powSuccStr`: the iterated structure isomorphism `(P e^{n+1}) a ≅ a` for a
  family `P` with composition isomorphisms only, without an identity isomorphism `P 𝟙 ≅ 𝟭`.
- `ProEtale.CondensedRing.WeilSheaf.pow`: a Weil sheaf for `e` as a Weil sheaf for `eⁿ`,
  functorially in `ProEtale.CondensedRing.WeilSheaf.powFunctor`.

## Main results

- `CategoryTheory.Iso.powStr_succ_eq_powSuccStr`: for an identity isomorphism compatible with the
  composition isomorphisms, `Iso.powStr` at `n + 1` is `Iso.powSuccStr` at `n`.
- `ProEtale.CondensedRing.WeilSheaf.pow_succ`: the Weil sheaf `F^{(n+1)}` is computed with
  `Iso.powSuccStr`, by the unit law `upperStarComp_id_left` of the pullbacks.

## Implementation notes

The recursions are carried out in the generic `CategoryTheory.Iso.powStr` and
`CategoryTheory.Iso.powSuccStr` and only then
instantiated with the pullbacks on module objects: done directly on module objects, the kernel
times out while checking the recursive definition. The iterates `e^{n+1}` of the Weil objects
of `Dᵇc(X)⟦ℚ̲̄_ℓ⟧` are computed with `Iso.powSuccStr`, since no identity isomorphism of the derived
pullback compatible with the other coherences is available there.

The coherence of `φ_F^{(n)}` with the iterated structure isomorphism
`CategoryTheory.Endofunctor.IsoAlgebra.strIterate`, through the iterated composition isomorphism
`(eⁿ)^* ≅ (e^*)ⁿ`, and the identity relating `φ_F^{(n+m)}` to `φ_F^{(n)}` and `φ_F^{(m)}` up to
the composition isomorphisms, are not proved here.

-/

@[expose] public section

universe v u

open CategoryTheory Endofunctor

open scoped CategoryTheory.Obj

namespace CategoryTheory.Iso

variable {C : Type u} [Category.{v} C] {X : C} (e : X ≅ X)

/-- The power `e.pow n = eⁿ` of an automorphism, defined recursively by `e⁰ = 𝟙` and
`e^{n+1} = eⁿ ≫ e`. -/
def pow (e : X ≅ X) : ℕ → (X ≅ X)
  | 0 => Iso.refl X
  | n + 1 => pow e n ≪≫ e

@[simp]
lemma pow_zero : e.pow 0 = Iso.refl X :=
  rfl

lemma pow_succ (n : ℕ) : e.pow (n + 1) = e.pow n ≪≫ e :=
  rfl

@[simp]
lemma pow_one : e.pow 1 = e :=
  Iso.refl_trans e

@[simp]
lemma pow_refl (n : ℕ) : (Iso.refl X).pow n = Iso.refl X := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ih, Iso.refl_trans]

/-- The powers `e.pow n` of an automorphism are the monoid powers `e.hom ^ n` in `End X`. -/
lemma pow_hom_eq_pow (n : ℕ) : (e.pow n).hom = (End.of e.hom ^ n).asHom := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, Iso.trans_hom, ih, _root_.pow_succ', End.mul_asHom]

/-- A morphism `s` with `e ≫ s = s` satisfies `eⁿ ≫ s = s`. -/
lemma pow_hom_comp_of_hom_comp {Y : C} {s : X ⟶ Y} (h : e.hom ≫ s = s) (n : ℕ) :
    (e.pow n).hom ≫ s = s := by
  induction n with
  | zero => exact Category.id_comp s
  | succ n ih => rw [pow_succ, Iso.trans_hom, Category.assoc, h, ih]

/-- The iterated structure isomorphism `(P eⁿ) a ≅ a` of an object `a` with an isomorphism
`φ : P e a ≅ a`, for a family of endofunctors `P g` indexed by the endomorphisms `g` of `X`,
contravariant up to an identity isomorphism `P 𝟙 ≅ 𝟭` and the composition isomorphisms
`P (f ≫ g) ≅ P g ⋙ P f`: it is the identity isomorphism at `a` for `n = 0`, and the composite
`P (eⁿ ≫ e) a ≅ P eⁿ (P e a) ≅ P eⁿ a ≅ a` of the composition isomorphism, `P eⁿ φ` and the
iterated structure isomorphism for `n`. -/
noncomputable def powStr {D : Type*} [Category D] (P : (X ⟶ X) → D ⥤ D)
    (id : P (𝟙 X) ≅ 𝟭 D) (comp : ∀ f g : X ⟶ X, P (f ≫ g) ≅ P g ⋙ P f) {a : D}
    (φ : (P e.hom).obj a ≅ a) : ∀ n : ℕ, (P (e.pow n).hom).obj a ≅ a
  | 0 => id.app a
  | n + 1 =>
    (comp (e.pow n).hom e.hom).app a ≪≫ (P (e.pow n).hom).mapIso φ ≪≫ powStr P id comp φ n

/-- The iterated structure isomorphisms are natural: a morphism `u : a ⟶ b` compatible with
`φ : P e a ≅ a` and `ψ : P e b ≅ b` is compatible with their iterates. -/
lemma powStr_hom_naturality {D : Type*} [Category D] (P : (X ⟶ X) → D ⥤ D)
    (id : P (𝟙 X) ≅ 𝟭 D) (comp : ∀ f g : X ⟶ X, P (f ≫ g) ≅ P g ⋙ P f) {a b : D}
    {φ : (P e.hom).obj a ≅ a} {ψ : (P e.hom).obj b ≅ b} (u : a ⟶ b)
    (hu : (P e.hom).map u ≫ ψ.hom = φ.hom ≫ u) (n : ℕ) :
    (P (e.pow n).hom).map u ≫ (e.powStr P id comp ψ n).hom =
      (e.powStr P id comp φ n).hom ≫ u := by
  induction n with
  | zero => exact id.hom.naturality u
  | succ n ih =>
    change (P ((e.pow n).hom ≫ e.hom)).map u ≫ (comp _ _).hom.app b ≫
        (P (e.pow n).hom).map ψ.hom ≫ (e.powStr P id comp ψ n).hom =
      ((comp _ _).hom.app a ≫ (P (e.pow n).hom).map φ.hom ≫
        (e.powStr P id comp φ n).hom) ≫ u
    rw [(comp _ _).hom.naturality_assoc, Functor.comp_map, ← Functor.map_comp_assoc, hu,
      Functor.map_comp_assoc, ih, Category.assoc, Category.assoc]

/-- The iterated structure isomorphism `(P eⁿ) a ≅ a` of an object `a` with an isomorphism
`φ : P e a ≅ a`, for a family of endofunctors `P g` indexed by the endomorphisms `g` of `X`,
contravariant up to the composition isomorphisms `P (f ≫ g) ≅ P g ⋙ P f`: it is `φ`, transported
along `𝟙 ≫ e = e`, for `n = 0`, and the composite `P (e^{n+1} ≫ e) a ≅ P e^{n+1} (P e a) ≅
P e^{n+1} a ≅ a` of the composition isomorphism, `P e^{n+1} φ` and the iterated structure
isomorphism for `n`.

Unlike `Iso.powStr` it needs no identity isomorphism `P 𝟙 ≅ 𝟭`; when one is given, compatible
with the composition isomorphisms, the two agree (`Iso.powStr_succ_eq_powSuccStr`). -/
noncomputable def powSuccStr {D : Type*} [Category D] (P : (X ⟶ X) → D ⥤ D)
    (comp : ∀ f g : X ⟶ X, P (f ≫ g) ≅ P g ⋙ P f) {a : D} (φ : (P e.hom).obj a ≅ a) :
    ∀ n : ℕ, (P (e.pow (n + 1)).hom).obj a ≅ a
  | 0 => eqToIso (congrArg (fun g ↦ (P g).obj a) (Category.id_comp e.hom)) ≪≫ φ
  | n + 1 =>
    (comp (e.pow (n + 1)).hom e.hom).app a ≪≫ (P (e.pow (n + 1)).hom).mapIso φ ≪≫
      powSuccStr P comp φ n

lemma powSuccStr_zero {D : Type*} [Category D] (P : (X ⟶ X) → D ⥤ D)
    (comp : ∀ f g : X ⟶ X, P (f ≫ g) ≅ P g ⋙ P f) {a : D} (φ : (P e.hom).obj a ≅ a) :
    e.powSuccStr P comp φ 0 =
      eqToIso (congrArg (fun g ↦ (P g).obj a) (Category.id_comp e.hom)) ≪≫ φ :=
  rfl

lemma powSuccStr_succ {D : Type*} [Category D] (P : (X ⟶ X) → D ⥤ D)
    (comp : ∀ f g : X ⟶ X, P (f ≫ g) ≅ P g ⋙ P f) {a : D} (φ : (P e.hom).obj a ≅ a) (n : ℕ) :
    e.powSuccStr P comp φ (n + 1) =
      (comp (e.pow (n + 1)).hom e.hom).app a ≪≫ (P (e.pow (n + 1)).hom).mapIso φ ≪≫
        e.powSuccStr P comp φ n :=
  rfl

/-- The iterated structure isomorphisms `Iso.powSuccStr` are natural: a morphism `u : a ⟶ b`
compatible with `φ : P e a ≅ a` and `ψ : P e b ≅ b` is compatible with their iterates. -/
lemma powSuccStr_hom_naturality {D : Type*} [Category D] (P : (X ⟶ X) → D ⥤ D)
    (comp : ∀ f g : X ⟶ X, P (f ≫ g) ≅ P g ⋙ P f) {a b : D} {φ : (P e.hom).obj a ≅ a}
    {ψ : (P e.hom).obj b ≅ b} (u : a ⟶ b) (hu : (P e.hom).map u ≫ ψ.hom = φ.hom ≫ u) (n : ℕ) :
    (P (e.pow (n + 1)).hom).map u ≫ (e.powSuccStr P comp ψ n).hom =
      (e.powSuccStr P comp φ n).hom ≫ u := by
  induction n with
  | zero =>
    have key : ∀ (g g' : X ⟶ X) (h : g = g'),
        (P g).map u ≫ eqToHom (congrArg (fun g ↦ (P g).obj b) h) =
          eqToHom (congrArg (fun g ↦ (P g).obj a) h) ≫ (P g').map u := by
      rintro g _ rfl
      simp
    change (P (𝟙 X ≫ e.hom)).map u ≫
        eqToHom (congrArg (fun g ↦ (P g).obj b) (Category.id_comp e.hom)) ≫ ψ.hom =
      (eqToHom (congrArg (fun g ↦ (P g).obj a) (Category.id_comp e.hom)) ≫ φ.hom) ≫ u
    rw [reassoc_of% key _ _ (Category.id_comp e.hom), hu, Category.assoc]
  | succ n ih =>
    change (P ((e.pow (n + 1)).hom ≫ e.hom)).map u ≫ (comp _ _).hom.app b ≫
        (P (e.pow (n + 1)).hom).map ψ.hom ≫ (e.powSuccStr P comp ψ n).hom =
      ((comp _ _).hom.app a ≫ (P (e.pow (n + 1)).hom).map φ.hom ≫
        (e.powSuccStr P comp φ n).hom) ≫ u
    rw [(comp _ _).hom.naturality_assoc, Functor.comp_map, ← Functor.map_comp_assoc, hu,
      Functor.map_comp_assoc, ih, Category.assoc, Category.assoc]

/-- For an identity isomorphism `P 𝟙 ≅ 𝟭` compatible with the composition isomorphism
`P (𝟙 ≫ e) ≅ P e ⋙ P 𝟙`, the iterated structure isomorphisms `Iso.powStr` for `n + 1` are
the iterated structure isomorphisms `Iso.powSuccStr` for `n`. -/
lemma powStr_succ_eq_powSuccStr {D : Type*} [Category D] (P : (X ⟶ X) → D ⥤ D)
    (id : P (𝟙 X) ≅ 𝟭 D) (comp : ∀ f g : X ⟶ X, P (f ≫ g) ≅ P g ⋙ P f) {a : D}
    (φ : (P e.hom).obj a ≅ a)
    (hid : comp (𝟙 X) e.hom ≪≫ Functor.isoWhiskerLeft (P e.hom) id ≪≫
      Functor.rightUnitor (P e.hom) = eqToIso (congrArg P (Category.id_comp e.hom))) (n : ℕ) :
    e.powStr P id comp φ (n + 1) = e.powSuccStr P comp φ n := by
  induction n with
  | zero =>
    have hid : (comp (𝟙 X) e.hom).hom.app a ≫ id.hom.app ((P e.hom).obj a) =
        eqToHom (congrArg (fun g ↦ (P g).obj a) (Category.id_comp e.hom)) := by
      simpa using congrArg (fun i ↦ i.hom.app a) hid
    ext
    change (comp (𝟙 X) e.hom).hom.app a ≫ (P (𝟙 X)).map φ.hom ≫ id.hom.app a =
      eqToHom (congrArg (fun g ↦ (P g).obj a) (Category.id_comp e.hom)) ≫ φ.hom
    rw [← hid, Category.assoc]
    exact congrArg _ (id.hom.naturality φ.hom)
  | succ n ih =>
    change (comp (e.pow (n + 1)).hom e.hom).app a ≪≫ (P (e.pow (n + 1)).hom).mapIso φ ≪≫
        e.powStr P id comp φ (n + 1) = _
    rw [ih]
    rfl

end CategoryTheory.Iso

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C : Type u} [Category.{v} C] {F : C ⥤ C}

/-- A morphism `IsoAlgebra.mk a Φ ⟶ IsoAlgebra.mk b Ψ`, given by a morphism `u : a ⟶ b` commuting
with the structure isomorphisms. -/
def mkHom {a b : C} {Φ : F.obj a ≅ a} {Ψ : F.obj b ≅ b} (u : a ⟶ b)
    (h : F.map u ≫ Ψ.hom = Φ.hom ≫ u) : mk a Φ ⟶ mk b Ψ :=
  ObjectProperty.homMk { f := u, h := h }

@[simp]
lemma mkHom_hom_f {a b : C} {Φ : F.obj a ≅ a} {Ψ : F.obj b ≅ b} (u : a ⟶ b)
    (h : F.map u ≫ Ψ.hom = Φ.hom ≫ u) : (mkHom u h).hom.f = u :=
  rfl

lemma mkHom_id {a : C} {Φ : F.obj a ≅ a} (h : F.map (𝟙 a) ≫ Φ.hom = Φ.hom ≫ 𝟙 a) :
    mkHom (𝟙 a) h = 𝟙 (mk a Φ) :=
  rfl

lemma mkHom_comp {a b c : C} {Φ : F.obj a ≅ a} {Ψ : F.obj b ≅ b} {Θ : F.obj c ≅ c} (u : a ⟶ b)
    (v : b ⟶ c) (hu : F.map u ≫ Ψ.hom = Φ.hom ≫ u) (hv : F.map v ≫ Θ.hom = Ψ.hom ≫ v)
    (huv : F.map (u ≫ v) ≫ Θ.hom = Φ.hom ≫ u ≫ v) :
    mkHom (u ≫ v) huv = mkHom u hu ≫ mkHom v hv :=
  rfl

end CategoryTheory.Endofunctor.IsoAlgebra

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] {X : Over (Spec (.of k))} {e : X ≅ X}

/-- A Weil sheaf `(F, φ_F)` for `e` as a Weil sheaf for `eⁿ`, with the iterated structure
isomorphism `φ_F^{(n)} : (eⁿ)^* F ≅ F`: `φ_F^{(0)}` is the identity isomorphism `upperStarId`
and `φ_F^{(n+1)}` is the composite `(eⁿ ≫ e)^* F ≅ (eⁿ)^* e^* F ≅ (eⁿ)^* F ≅ F` of the composition
isomorphism `upperStarComp`, `(eⁿ)^* φ_F` and `φ_F^{(n)}`. -/
noncomputable def WeilSheaf.pow (F : WeilSheaf ℓ e) (n : ℕ) : WeilSheaf ℓ (e.pow n) :=
  IsoAlgebra.mk F.carrier
    (e.powStr (fun g ↦ (g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
      (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left)
      (fun f g ↦ upperStarComp (Profinite.padicAlgClRingObj ℓ) f.left g.left) F.str n)

@[simp]
lemma WeilSheaf.pow_carrier (F : WeilSheaf ℓ e) (n : ℕ) :
    (WeilSheaf.pow ℓ F n).carrier = F.carrier :=
  IsoAlgebra.mk_carrier _ _

variable (e) in
/-- A Weil sheaf for `e` as a Weil sheaf for `eⁿ` (`WeilSheaf.pow`), as a functor: a morphism of
Weil sheaves for `e` is compatible with the iterated structure isomorphisms. -/
noncomputable def WeilSheaf.powFunctor (n : ℕ) : WeilSheaf ℓ e ⥤ WeilSheaf ℓ (e.pow n) where
  obj F := WeilSheaf.pow ℓ F n
  map {F G} φ := IsoAlgebra.mkHom φ.hom.f
    (e.powStr_hom_naturality (fun g ↦ (g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
      (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left)
      (fun f g ↦ upperStarComp (Profinite.padicAlgClRingObj ℓ) f.left g.left) (φ := F.str)
      (ψ := G.str) φ.hom.f φ.hom.h n)
  map_id _ := IsoAlgebra.mkHom_id _
  map_comp _ _ := IsoAlgebra.mkHom_comp _ _ _ _ _

@[simp]
lemma WeilSheaf.powFunctor_obj (n : ℕ) (F : WeilSheaf ℓ e) :
    (WeilSheaf.powFunctor ℓ e n).obj F = WeilSheaf.pow ℓ F n :=
  rfl

/-- The composition isomorphism `(𝟙 ≫ t)^* ≅ t^* ⋙ 𝟙^*` of the pullbacks of module objects,
followed by the identity isomorphism `𝟙^* ≅ 𝟭`, is the transport along `𝟙 ≫ t = t`. -/
lemma upperStarComp_id_trans_isoWhiskerLeft_upperStarId {Y Z : Scheme.{u}} (t : Y ⟶ Z) :
    upperStarComp (Profinite.padicAlgClRingObj ℓ) (𝟙 Y) t ≪≫
        Functor.isoWhiskerLeft _ (upperStarId (Profinite.padicAlgClRingObj ℓ) Y) ≪≫
          Functor.rightUnitor _ =
      upperStarCongr (Profinite.padicAlgClRingObj ℓ) (Category.id_comp t) := by
  rw [upperStarComp_id_left]
  ext M
  simp

variable (e) in
/-- The `(n + 1)`-st iterated structure isomorphism of a Weil sheaf is `Iso.powSuccStr`, which
does not involve the identity isomorphism `upperStarId`. -/
lemma powStr_succ_upperStar_eq_powSuccStr
    {M : Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)}
    (φ : (e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M ≅ M) (n : ℕ) :
    e.powStr (fun g ↦ (g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
        (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left)
        (fun f g ↦ upperStarComp (Profinite.padicAlgClRingObj ℓ) f.left g.left) φ (n + 1) =
      e.powSuccStr (fun g ↦ (g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
        (fun f g ↦ upperStarComp (Profinite.padicAlgClRingObj ℓ) f.left g.left) φ n :=
  e.powStr_succ_eq_powSuccStr (fun g ↦ (g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
    (upperStarId (Profinite.padicAlgClRingObj ℓ) X.left)
    (fun f g ↦ upperStarComp (Profinite.padicAlgClRingObj ℓ) f.left g.left) φ
    (upperStarComp_id_trans_isoWhiskerLeft_upperStarId ℓ e.hom.left) n

/-- A Weil sheaf as a Weil sheaf for `e^{n+1}` has the iterated structure isomorphism
`Iso.powSuccStr`. -/
lemma WeilSheaf.pow_succ (F : WeilSheaf ℓ e) (n : ℕ) :
    WeilSheaf.pow ℓ F (n + 1) = IsoAlgebra.mk F.carrier
      (e.powSuccStr (fun g ↦ (g.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧)
        (fun f g ↦ upperStarComp (Profinite.padicAlgClRingObj ℓ) f.left g.left) F.str n) :=
  congrArg (IsoAlgebra.mk F.carrier) (powStr_succ_upperStar_eq_powSuccStr ℓ e F.str n)

end AlgebraicGeometry.ProEtale.CondensedRing
