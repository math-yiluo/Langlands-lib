/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RepresentationTheory.DiscreteModule.Induction
public import WeilConjectures.RepresentationTheory.DiscreteModule.Sylow
public import WeilConjectures.Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# A degree-two criterion for the cohomological dimension of a profinite group

Let `G` be a profinite group and `ℓ` a prime such that `H²(K, 𝔽_ℓ) = 0` for every open subgroup
`K` of `G`. Then `Hⁿ(G, M) = 0` for every `n ≥ 2` and every `ℓ`-primary discrete `G`-module `M`.

For finite `M`, an open subgroup `K` of index prime to `ℓ` acts on `M` through an `ℓ`-group, so
`M|_K` is an iterated extension of trivial modules `𝔽_ℓ` and `H²(K, M) = 0`; restriction followed
by corestriction is multiplication by the index, hence `H²(G, M) = 0`. A general `M` is the
union of its finite submodules; we show directly, by an explicit computation of `H²` through
coinduced modules, that `H²` vanishes on such a union. Finally the coinduced modules
`C^sm(G, M)` are acyclic, so a dimension shift gives all degrees `n ≥ 2`.

## Main statements

- `DiscreteModule.subsingleton_H_coind₁`: coinduced modules are acyclic.
- `DiscreteModule.subsingleton_H_two_iff`: `H²(G, X) = 0` in terms of invariants of the
  iterated cokernels `C^sm(G, X) / X`.
- `DiscreteModule.subsingleton_H_two_of_forall_finite`: `H²` of a union.
- `DiscreteModule.subsingleton_H_two_of_finite`: the finite case, by restriction–corestriction.
- `DiscreteModule.subsingleton_H_of_two_le`: the criterion.
-/

@[expose] public section

universe w u v

open CategoryTheory Limits Action

namespace DiscreteModule

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section toolkit

/-- A short complex of discrete modules which is exact on the underlying abelian groups, with
injective first map and surjective second map, is short exact. -/
lemma shortExact_of_forget {S : ShortComplex (DiscreteModule.{w} G)}
    (hf : Function.Injective S.f.hom.hom.hom) (hg : Function.Surjective S.g.hom.hom.hom)
    (hfg : ∀ x, S.g.hom.hom.hom x = 0 → ∃ y, S.f.hom.hom.hom y = x) : S.ShortExact where
  exact := by
    rw [← S.exact_map_iff_of_faithful (forget₂Ab.{w} G), ShortComplex.ab_exact_iff]
    exact hfg
  mono_f := (forget₂Ab.{w} G).mono_of_mono_map ((AddCommGrpCat.mono_iff_injective _).2 hf)
  epi_g := (forget₂Ab.{w} G).epi_of_epi_map ((AddCommGrpCat.epi_iff_surjective _).2 hg)

/-- Vanishing of `Ext` into the middle term of a short exact sequence. -/
lemma subsingleton_ext_of_shortExact {C : Type*} [Category* C] [Abelian C] [HasExt.{w} C]
    {X : C} {S : ShortComplex C} (hS : S.ShortExact) {n : ℕ}
    (h₁ : Subsingleton (Abelian.Ext X S.X₁ n)) (h₃ : Subsingleton (Abelian.Ext X S.X₃ n)) :
    Subsingleton (Abelian.Ext X S.X₂ n) := by
  refine ⟨fun a b ↦ ?_⟩
  have key (x : Abelian.Ext X S.X₂ n) : x = 0 := by
    obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₂ X hS x (Subsingleton.elim _ _)
    rw [← hy, Subsingleton.elim y 0, Abelian.Ext.zero_comp]
  rw [key a, key b]

/-- Dimension shifting: `Extⁿ⁺¹(X, S.X₁)` is a quotient of `Extⁿ(X, S.X₃)` when
`Extⁿ⁺¹(X, S.X₂) = 0`. -/
lemma subsingleton_ext_succ_of_shortExact {C : Type*} [Category* C] [Abelian C] [HasExt.{w} C]
    {X : C} {S : ShortComplex C} (hS : S.ShortExact) {n : ℕ}
    (h₂ : Subsingleton (Abelian.Ext X S.X₂ (n + 1))) (h₃ : Subsingleton (Abelian.Ext X S.X₃ n)) :
    Subsingleton (Abelian.Ext X S.X₁ (n + 1)) := by
  refine ⟨fun a b ↦ ?_⟩
  have key (x : Abelian.Ext X S.X₁ (n + 1)) : x = 0 := by
    obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₁ X hS x (Subsingleton.elim _ _) rfl
    rw [← hy, Subsingleton.elim y 0, Abelian.Ext.zero_comp]
  rw [key a, key b]

end toolkit

section coind₁

/-- **Coinduced modules are acyclic.** `Hⁿ(G, C^sm(G, A)) = 0` for `n ≥ 1`: by the
`Ext`-adjunction for the exact functors `forget ⊣ coind₁` it is `Extⁿ(ℤ, A)` computed among
abelian groups, which vanishes as `ℤ` is projective. -/
lemma subsingleton_H_coind₁ (A : AddCommGrpCat.{max u w}) (n : ℕ) :
    Subsingleton (H G ((coind₁ G).obj A) (n + 1)) := by
  let := hasExt_of_enoughInjectives.{max u w} AddCommGrpCat.{max u w}
  have e := (coind₁Adjunction.{w} G).extAddEquiv (intTrivial G) A (n + 1)
  have : Projective ((forget₂Ab.{w} G).obj (intTrivial G)) :=
    AddCommGrpCat.projective_of_uliftInt
  refine ⟨fun a b ↦ e.injective ?_⟩
  rw [Abelian.Ext.eq_zero_of_projective (e a), Abelian.Ext.eq_zero_of_projective (e b)]

end coind₁

section quotient

variable (X : DiscreteModule.{w} G) (S : AddSubgroup X.obj.V)
  (hS : ∀ g : G, ∀ x ∈ S, (X.obj.ρ g).asHom.hom x ∈ S)

/-- The quotient of a discrete module by a stable subgroup. -/
@[simps]
def quotientAction : Action AddCommGrpCat.{max u w} G where
  V := AddCommGrpCat.of (X.obj.V ⧸ S)
  ρ :=
    { toFun g := .of <| AddCommGrpCat.ofHom
        (QuotientAddGroup.map S S (X.obj.ρ g).asHom.hom fun x hx ↦ hS g x hx)
      map_one' := End.ext <| AddCommGrpCat.ext fun q ↦ QuotientAddGroup.induction_on q fun x ↦ by
        simp [End.one_asHom]
      map_mul' a b := End.ext <| AddCommGrpCat.ext fun q ↦
        QuotientAddGroup.induction_on q fun x ↦ by simp [End.mul_asHom] }

/-- The quotient of a discrete module by a stable subgroup. -/
def quotient : DiscreteModule.{w} G :=
  ⟨quotientAction X S hS, fun q ↦ QuotientAddGroup.induction_on q fun x ↦
    Subgroup.isOpen_mono (H₁ := X.obj.stabilizer x) (fun g (hg : _ = _) ↦ by
      change QuotientAddGroup.mk ((X.obj.ρ g).asHom.hom x) = _
      rw [hg]) (X.isOpen_stabilizer x)⟩

/-- The projection onto the quotient. -/
def quotientπ : X ⟶ quotient X S hS :=
  ObjectProperty.homMk
    { hom := AddCommGrpCat.ofHom (QuotientAddGroup.mk' S)
      comm _ := rfl }

@[simp]
lemma quotientπ_apply (x : X.obj.V) :
    (quotientπ X S hS).hom.hom.hom x = QuotientAddGroup.mk x :=
  rfl

lemma quotient_ρ_mk (g : G) (x : X.obj.V) :
    ((quotient X S hS).obj.ρ g).asHom.hom (QuotientAddGroup.mk x) =
      QuotientAddGroup.mk ((X.obj.ρ g).asHom.hom x) :=
  rfl


end quotient

lemma subsingleton_H_of_subsingleton (X : DiscreteModule.{w} G) [Subsingleton X.obj.V] (n : ℕ) :
    Subsingleton (H G X n) := by
  have hX : IsZero X := by
    rw [IsZero.iff_id_eq_zero]
    ext x
    exact Subsingleton.elim _ _
  refine ⟨fun a b ↦ ?_⟩
  rw [← Abelian.Ext.comp_mk₀_id a, ← Abelian.Ext.comp_mk₀_id b, hX.eq_of_src (𝟙 X) 0,
    Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero, Abelian.Ext.comp_zero]

/-- A predicate saying that every element of a discrete module is killed by a power of `ℓ`. -/
def IsPrimary (ℓ : ℕ) (X : DiscreteModule.{w} G) : Prop :=
  ∀ x : X.obj.V, ∃ j : ℕ, ℓ ^ j • x = 0

section finite

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

variable (G) in
/-- The trivial discrete module `𝔽_ℓ`. -/
abbrev trivialZMod : DiscreteModule.{w} G :=
  trivial G (AddCommGrpCat.of (ULift.{max u w} (ZMod ℓ)))

/-- The additive map `𝔽_ℓ ⟶ X`, `1 ↦ x`, for `x` killed by `ℓ`. -/
def zmodHom {A : Type*} [AddCommGroup A] (x : A) (hx : ℓ • x = 0) :
    ULift.{v} (ZMod ℓ) →+ A :=
  (ZMod.lift ℓ ⟨zmultiplesHom _ x, by simp [hx]⟩).comp AddEquiv.ulift.toAddMonoidHom

lemma zmodHom_intCast {A : Type*} [AddCommGroup A] (x : A) (hx : ℓ • x = 0) (n : ℤ) :
    zmodHom.{v} ℓ x hx (ULift.up (n : ZMod ℓ)) = n • x := by
  change ZMod.lift ℓ ⟨zmultiplesHom A x, by simp [hx]⟩ ((n : ZMod ℓ)) = n • x
  rw [ZMod.lift_coe]
  simp

/-- The inclusion `𝔽_ℓ ⟶ X`, `1 ↦ x`, of an invariant element killed by `ℓ`. -/
def ofInvariant (X : DiscreteModule.{w} G) (x : X.obj.V) (hx : ℓ • x = 0)
    (hxg : ∀ g : G, (X.obj.ρ g).asHom.hom x = x) : trivialZMod.{w} G ℓ ⟶ X :=
  ObjectProperty.homMk
    { hom := AddCommGrpCat.ofHom (zmodHom.{max u w} ℓ x hx)
      comm g := AddCommGrpCat.ext fun a ↦ by
        obtain ⟨n, hn⟩ := ZMod.intCast_surjective a.down
        obtain rfl : a = ULift.up (n : ZMod ℓ) := ULift.ext hn.symm
        change zmodHom.{max u w} ℓ x hx (ULift.up (n : ZMod ℓ)) =
          (X.obj.ρ g).asHom.hom (zmodHom.{max u w} ℓ x hx (ULift.up (n : ZMod ℓ)))
        rw [zmodHom_intCast, map_zsmul, hxg g] }

omit [IsTopologicalGroup G] in
lemma ofInvariant_apply_intCast (X : DiscreteModule.{w} G) (x : X.obj.V) (hx : ℓ • x = 0)
    (hxg : ∀ g : G, (X.obj.ρ g).asHom.hom x = x) (n : ℤ) :
    (ofInvariant ℓ X x hx hxg).hom.hom.hom (ULift.up (n : ZMod ℓ)) = n • x :=
  zmodHom_intCast.{max u w} ℓ x hx n

omit [IsTopologicalGroup G] in
lemma injective_ofInvariant (X : DiscreteModule.{w} G) (x : X.obj.V) (hx : ℓ • x = 0)
    (hxg : ∀ g : G, (X.obj.ρ g).asHom.hom x = x) (hx0 : x ≠ 0) :
    Function.Injective (ofInvariant ℓ X x hx hxg).hom.hom.hom := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨a⟩ ha
  by_contra h
  have ha0 : a ≠ 0 := fun h' ↦ h (by rw [h']; rfl)
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective a⁻¹
  have h1 : ((n * a : ZMod ℓ)) = 1 := by
    rw [hn]
    exact inv_mul_cancel₀ (G₀ := ZMod ℓ) ha0
  obtain ⟨m, hm⟩ := ZMod.intCast_surjective a
  have : (ofInvariant ℓ X x hx hxg).hom.hom.hom (ULift.up (n * a : ZMod ℓ)) = n • 0 := by
    rw [← ha, ← hm, ← Int.cast_mul, ofInvariant_apply_intCast, ofInvariant_apply_intCast,
      mul_smul]
  rw [h1, smul_zero, show (1 : ZMod ℓ) = ((1 : ℤ) : ZMod ℓ) by simp,
    ofInvariant_apply_intCast, one_smul] at this
  exact hx0 this

/-- **Modules over an `ℓ`-group.** Suppose that `G` acts on finite `ℓ`-primary modules through
an `ℓ`-group: the normal subgroup `N` acts trivially and every element of `G` has an `ℓ`-power in
`N`. If `H²(G, 𝔽_ℓ) = 0`, then `H²(G, X) = 0` for every such `X`: a nonzero `X` contains a
copy of `𝔽_ℓ` spanned by a fixed vector, and we argue by induction on `#X`. -/
theorem subsingleton_H_two_of_forall_pow_mem (N : Subgroup G) [N.Normal]
    (hpow : ∀ k : G, ∃ j : ℕ, k ^ ℓ ^ j ∈ N) (h2 : Subsingleton (H G (trivialZMod.{w} G ℓ) 2))
    (n : ℕ) (X : DiscreteModule.{w} G) [Finite X.obj.V] (hn : Nat.card X.obj.V = n)
    (hN : ∀ k ∈ N, ∀ x : X.obj.V, (X.obj.ρ k).asHom.hom x = x) (hX : IsPrimary ℓ X) :
    Subsingleton (H G X 2) := by
  induction n using Nat.strong_induction_on generalizing X with
  | _ n ih =>
  by_cases htriv : Subsingleton X.obj.V
  · exact subsingleton_H_of_subsingleton X 2
  rw [not_subsingleton_iff_nontrivial] at htriv
  let := X.obj.distribMulAction
  obtain ⟨x, hx0, hxℓ, hxg⟩ := exists_ne_zero_nsmul_eq_zero_smul_eq_of_isPGroup ℓ N hN hpow hX
  let S := AddSubgroup.zmultiples x
  have hS : ∀ g : G, ∀ y ∈ S, (X.obj.ρ g).asHom.hom y ∈ S := by
    rintro g _ ⟨m, rfl⟩
    exact ⟨m, by rw [map_zsmul]; exact congrArg (m • ·) (hxg g).symm⟩
  have hzero : ofInvariant ℓ X x hxℓ hxg ≫ quotientπ X S hS = 0 := by
    ext a
    obtain ⟨m, hm⟩ := ZMod.intCast_surjective a.down
    obtain rfl : a = ULift.up (m : ZMod ℓ) := ULift.ext hm.symm
    change QuotientAddGroup.mk ((ofInvariant ℓ X x hxℓ hxg).hom.hom.hom _) = 0
    rw [ofInvariant_apply_intCast, QuotientAddGroup.eq_zero_iff]
    exact ⟨m, rfl⟩
  let T := ShortComplex.mk _ _ hzero
  have hT : T.ShortExact := by
    refine shortExact_of_forget (injective_ofInvariant ℓ X x hxℓ hxg hx0)
      QuotientAddGroup.mk_surjective fun y hy ↦ ?_
    obtain ⟨m, rfl⟩ := (QuotientAddGroup.eq_zero_iff y).1 hy
    exact ⟨ULift.up (m : ZMod ℓ), ofInvariant_apply_intCast ℓ X x hxℓ hxg m⟩
  refine subsingleton_ext_of_shortExact hT h2 ?_
  have : Finite (quotient X S hS).obj.V :=
    Finite.of_surjective _ (QuotientAddGroup.mk_surjective (s := S))
  refine ih _ ?_ (quotient X S hS) rfl ?_ ?_
  · rw [← hn, AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup S]
    have h1 : 1 < Nat.card S := by
      have : Nontrivial S := ⟨⟨0, ⟨x, AddSubgroup.mem_zmultiples x⟩, fun h ↦ hx0
        (congrArg Subtype.val h).symm⟩⟩
      exact Finite.one_lt_card_iff_nontrivial.2 this
    have h2 : 0 < Nat.card (X.obj.V ⧸ S) := Nat.card_pos
    change Nat.card (X.obj.V ⧸ S) < _
    nlinarith
  · intro k hk q
    induction q using QuotientAddGroup.induction_on with
    | H y => exact congrArg QuotientAddGroup.mk (hN k hk y)
  · intro q
    induction q using QuotientAddGroup.induction_on with
    | H y =>
      obtain ⟨j, hj⟩ := hX y
      exact ⟨j, by rw [← QuotientAddGroup.mk_nsmul, hj, QuotientAddGroup.mk_zero]⟩

end finite

section toolkit₂

variable {C : Type*} [Category* C] [Abelian C] [HasExt.{w} C] {X : C} {S : ShortComplex C}

/-- `Extⁿ(X, S.X₃) = 0` when `Extⁿ(X, S.X₂) = 0` and `Extⁿ⁺¹(X, S.X₁) = 0`. -/
lemma subsingleton_ext_of_shortExact' (hS : S.ShortExact) {n : ℕ}
    (h₂ : Subsingleton (Abelian.Ext X S.X₂ n)) (h₁ : Subsingleton (Abelian.Ext X S.X₁ (n + 1))) :
    Subsingleton (Abelian.Ext X S.X₃ n) := by
  refine ⟨fun a b ↦ ?_⟩
  have key (x : Abelian.Ext X S.X₃ n) : x = 0 := by
    obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₃ X hS x rfl (Subsingleton.elim _ _)
    rw [← hy, Subsingleton.elim y 0, Abelian.Ext.zero_comp]
  rw [key a, key b]

/-- If `Ext¹(X, S.X₂) = 0`, then `Ext¹(X, S.X₁) = 0` if and only if every morphism
`X ⟶ S.X₃` lifts to `S.X₂`. -/
lemma subsingleton_ext_one_iff (hS : S.ShortExact) (h : Subsingleton (Abelian.Ext X S.X₂ 1)) :
    Subsingleton (Abelian.Ext X S.X₁ 1) ↔ ∀ φ : X ⟶ S.X₃, ∃ ψ : X ⟶ S.X₂, ψ ≫ S.g = φ := by
  constructor
  · intro h₁ φ
    obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₃ X hS (Abelian.Ext.mk₀ φ) (zero_add 1)
      (Subsingleton.elim _ _)
    obtain ⟨ψ, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 y
    refine ⟨ψ, (Abelian.Ext.mk₀_bijective _ _).1 ?_⟩
    rw [← Abelian.Ext.mk₀_comp_mk₀]
    exact hy
  · intro hlift
    refine ⟨fun a b ↦ ?_⟩
    have key (x : Abelian.Ext X S.X₁ 1) : x = 0 := by
      obtain ⟨y, hy⟩ := Abelian.Ext.covariant_sequence_exact₁ X hS x (Subsingleton.elim _ _)
        (zero_add 1)
      obtain ⟨φ, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).2 y
      obtain ⟨ψ, rfl⟩ := hlift φ
      rw [← hy, ← Abelian.Ext.mk₀_comp_mk₀, Abelian.Ext.comp_assoc_of_second_deg_zero,
        hS.comp_extClass, Abelian.Ext.comp_zero]
    rw [key a, key b]

end toolkit₂

omit [IsTopologicalGroup G] in
/-- Morphisms from `ℤ` lift along `p` if and only if invariant elements lift to invariant
elements. -/
lemma forall_exists_comp_eq_iff {Y Z : DiscreteModule.{w} G} (p : Y ⟶ Z) :
    (∀ φ : intTrivial G ⟶ Z, ∃ ψ : intTrivial G ⟶ Y, ψ ≫ p = φ) ↔
      ∀ z : Z.obj.V, (∀ g, (Z.obj.ρ g).asHom.hom z = z) →
        ∃ y : Y.obj.V, (∀ g, (Y.obj.ρ g).asHom.hom y = y) ∧ p.hom.hom.hom y = z := by
  constructor
  · intro h z hz
    obtain ⟨ψ, hψ⟩ := h ((homIntTrivialEquiv Z).symm ⟨z, hz⟩)
    refine ⟨(homIntTrivialEquiv Y ψ).1, (homIntTrivialEquiv Y ψ).2, ?_⟩
    have := congrArg (fun φ ↦ (homIntTrivialEquiv Z φ).1) hψ
    simp only [AddEquiv.apply_symm_apply] at this
    exact this
  · intro h φ
    obtain ⟨y, hy, hpy⟩ := h (homIntTrivialEquiv Z φ).1 (homIntTrivialEquiv Z φ).2
    refine ⟨(homIntTrivialEquiv Y).symm ⟨y, hy⟩, (homIntTrivialEquiv Z).injective
      (Subtype.ext ?_)⟩
    change p.hom.hom.hom ((homIntTrivialEquiv Y ((homIntTrivialEquiv Y).symm ⟨y, hy⟩)).1) = _
    rw [AddEquiv.apply_symm_apply]
    exact hpy

section coker₁

variable (X : DiscreteModule.{w} G)

/-- The embedding `X ⟶ C^sm(G, X)`, `x ↦ (g ↦ g • x)`. -/
def toCoind₁ : X ⟶ (coind₁ G).obj X.obj.V :=
  coind₁Lift (𝟙 _)

@[simp]
lemma toCoind₁_apply (x : X.obj.V) (g : G) :
    ((toCoind₁ X).hom.hom.hom x).1 g = (X.obj.ρ g).asHom.hom x :=
  rfl

lemma injective_toCoind₁ : Function.Injective (toCoind₁ X).hom.hom.hom :=
  injective_coind₁Lift _ fun _ _ h ↦ h

/-- The image of `X` in `C^sm(G, X)`. -/
def toCoind₁Range : AddSubgroup ((coind₁ G).obj X.obj.V).obj.V :=
  (toCoind₁ X).hom.hom.hom.range

lemma mem_toCoind₁Range_iff (f : ((coind₁ G).obj X.obj.V).obj.V) :
    f ∈ toCoind₁Range X ↔ ∃ x, ∀ g, f.1 g = (X.obj.ρ g).asHom.hom x := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, fun g ↦ rfl⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext (funext fun g ↦ (hx g).symm)⟩

lemma toCoind₁Range_stable (g : G) (f : ((coind₁ G).obj X.obj.V).obj.V)
    (hf : f ∈ toCoind₁Range X) :
    (((coind₁ G).obj X.obj.V).obj.ρ g).asHom.hom f ∈ toCoind₁Range X := by
  obtain ⟨x, rfl⟩ := hf
  exact ⟨(X.obj.ρ g).asHom.hom x, hom_comm_apply (toCoind₁ X).hom g x⟩

/-- The cokernel `C^sm(G, X) / X` of the embedding of `X` into its coinduced module. -/
def coker₁ : DiscreteModule.{w} G :=
  quotient _ (toCoind₁Range X) (toCoind₁Range_stable X)

/-- The projection `C^sm(G, X) ⟶ C^sm(G, X) / X`. -/
def coker₁π : (coind₁ G).obj X.obj.V ⟶ coker₁ X :=
  quotientπ _ _ (toCoind₁Range_stable X)

@[simp]
lemma coker₁π_apply (f : ((coind₁ G).obj X.obj.V).obj.V) :
    (coker₁π X).hom.hom.hom f = (QuotientAddGroup.mk f : (coker₁ X).obj.V) :=
  rfl

/-- The short complex `X ⟶ C^sm(G, X) ⟶ C^sm(G, X) / X`. -/
def shortComplex₁ : ShortComplex (DiscreteModule.{w} G) :=
  ShortComplex.mk (toCoind₁ X) (coker₁π X) (by
    ext x
    change QuotientAddGroup.mk ((toCoind₁ X).hom.hom.hom x) = 0
    exact (QuotientAddGroup.eq_zero_iff _).2 ⟨x, rfl⟩)

lemma shortExact₁ : (shortComplex₁ X).ShortExact :=
  shortExact_of_forget (injective_toCoind₁ X) QuotientAddGroup.mk_surjective
    fun y hy ↦ (QuotientAddGroup.eq_zero_iff y).1 hy

lemma coker₁_ρ_mk (g : G) (f : ((coind₁ G).obj X.obj.V).obj.V) :
    ((coker₁ X).obj.ρ g).asHom.hom (QuotientAddGroup.mk f) =
      (QuotientAddGroup.mk ((((coind₁ G).obj X.obj.V).obj.ρ g).asHom.hom f) : (coker₁ X).obj.V) :=
  rfl

lemma coker₁_mk_eq_mk_iff (f f' : ((coind₁ G).obj X.obj.V).obj.V) :
    (QuotientAddGroup.mk f : (coker₁ X).obj.V) = QuotientAddGroup.mk f' ↔
      ∃ y, ∀ x, f.1 x - f'.1 x = (X.obj.ρ x).asHom.hom y := by
  rw [QuotientAddGroup.eq_iff_sub_mem, mem_toCoind₁Range_iff]
  exact Iff.rfl

/-- `H²(G, X)` vanishes if and only if every invariant element of `C^sm(G, C) / C`, with
`C = C^sm(G, X) / X`, lifts to an invariant element of `C^sm(G, C)`. -/
lemma subsingleton_H_two_iff :
    Subsingleton (H G X 2) ↔ ∀ φ : intTrivial G ⟶ coker₁ (coker₁ X),
      ∃ ψ : intTrivial G ⟶ (coind₁ G).obj (coker₁ X).obj.V,
        ψ ≫ coker₁π (coker₁ X) = φ := by
  refine Iff.trans ?_
    (subsingleton_ext_one_iff (shortExact₁ (coker₁ X)) (subsingleton_H_coind₁ _ 0))
  constructor
  · intro h
    exact subsingleton_ext_of_shortExact' (shortExact₁ X) (subsingleton_H_coind₁ _ 0) h
  · intro h
    exact subsingleton_ext_succ_of_shortExact (shortExact₁ X) (subsingleton_H_coind₁ _ 1) h

end coker₁

section sub

variable (X : DiscreteModule.{w} G) (S : AddSubgroup X.obj.V)
  (hS : ∀ g : G, ∀ x ∈ S, (X.obj.ρ g).asHom.hom x ∈ S)

/-- The action of `G` on a stable subgroup. -/
@[simps]
def subAction : Action AddCommGrpCat.{max u w} G where
  V := AddCommGrpCat.of S
  ρ :=
    { toFun g := .of <| AddCommGrpCat.ofHom (((X.obj.ρ g).asHom.hom.comp S.subtype).codRestrict S
        fun x ↦ hS g x x.2)
      map_one' := End.ext <| AddCommGrpCat.ext fun x ↦ Subtype.ext (by simp [End.one_asHom])
      map_mul' a b := End.ext <| AddCommGrpCat.ext fun x ↦
        Subtype.ext (by simp [End.mul_asHom]) }

/-- The discrete submodule given by a stable subgroup. -/
def sub : DiscreteModule.{w} G :=
  ⟨subAction X S hS, fun x ↦ Subgroup.isOpen_mono (H₁ := X.obj.stabilizer x.1)
    (fun _ (hg : _ = _) ↦ Subtype.ext hg) (X.isOpen_stabilizer x.1)⟩

/-- Restriction of the values of a smooth function lying in `S`. -/
def smoothFunctionsCodRestrict (φ : smoothFunctions G X.obj.V) (h : ∀ y, φ.1 y ∈ S) :
    smoothFunctions G S :=
  ⟨fun y ↦ ⟨φ.1 y, h y⟩, Subgroup.isOpen_mono (H₁ := rightStab G φ.1)
    (fun _ hg x ↦ Subtype.ext (hg x)) φ.2⟩

lemma smoothFunctionsMap_codRestrict (φ : smoothFunctions G X.obj.V) (h : ∀ y, φ.1 y ∈ S) :
    smoothFunctionsMap S.subtype (smoothFunctionsCodRestrict X S φ h) = φ :=
  rfl

/-- The map `C^sm(G, S) / S ⟶ C^sm(G, X) / X`. -/
def coker₁SubMap : (coker₁ (sub X S hS)).obj.V →+ (coker₁ X).obj.V :=
  QuotientAddGroup.map _ _ (smoothFunctionsMap S.subtype) (by
    rintro _ ⟨x, rfl⟩
    exact ⟨x.1, rfl⟩)

lemma coker₁SubMap_mk (f : ((coind₁ G).obj (sub X S hS).obj.V).obj.V) :
    coker₁SubMap X S hS (QuotientAddGroup.mk f) =
      (QuotientAddGroup.mk (smoothFunctionsMap S.subtype f) : (coker₁ X).obj.V) :=
  rfl

lemma coker₁SubMap_ρ (g : G) (c : (coker₁ (sub X S hS)).obj.V) :
    coker₁SubMap X S hS (((coker₁ (sub X S hS)).obj.ρ g).asHom.hom c) =
      ((coker₁ X).obj.ρ g).asHom.hom (coker₁SubMap X S hS c) := by
  obtain ⟨f, rfl⟩ := QuotientAddGroup.mk_surjective c
  rfl

lemma injective_coker₁SubMap : Function.Injective (coker₁SubMap X S hS) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨f, rfl⟩ := QuotientAddGroup.mk_surjective c
  rw [coker₁SubMap_mk, QuotientAddGroup.eq_zero_iff, mem_toCoind₁Range_iff] at hc
  obtain ⟨m, hm⟩ := hc
  rw [QuotientAddGroup.eq_zero_iff, mem_toCoind₁Range_iff]
  refine ⟨f.1 1, fun x ↦ Subtype.ext ?_⟩
  have hx : Subtype.val (f.1 x) = (X.obj.ρ x).asHom.hom m := hm x
  have h1 : Subtype.val (f.1 1) = (X.obj.ρ 1).asHom.hom m := hm 1
  change Subtype.val (f.1 x) = (X.obj.ρ x).asHom.hom (Subtype.val (f.1 1))
  rw [hx, h1, ρ_one_apply]

end sub

section compact

variable [CompactSpace G]

/-- A function on a compact group which is invariant under right translation by an open
subgroup takes finitely many values. -/
lemma finite_range_of_forall_mul_eq {A : Type*} (f : G → A) (U : Subgroup G)
    (hU : IsOpen (U : Set G)) (hf : ∀ x, ∀ u ∈ U, f (x * u) = f x) : (Set.range f).Finite := by
  have := Subgroup.quotient_finite_of_isOpen U hU
  let F : G ⧸ U → A := Quotient.lift (s := QuotientGroup.leftRel U) f fun a b hab ↦ by
    simpa using (hf a _ (QuotientGroup.leftRel_apply.1 hab)).symm
  refine (Set.finite_range F).subset ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨QuotientGroup.mk x, rfl⟩

lemma finite_range_smoothFunctions {A : Type*} [AddCommGroup A] (f : smoothFunctions G A) :
    (Set.range f.1).Finite :=
  finite_range_of_forall_mul_eq f.1 _ f.2 fun x _ hu ↦ hu x

/-- **`H²` of a union.** Let `G` be compact and `M` a discrete `G`-module such that every
finite subset of `M` is contained in a stable subgroup `S` with `H²(G, S) = 0`. Then
`H²(G, M) = 0`. -/
theorem subsingleton_H_two_of_forall_finite (M : DiscreteModule.{w} G)
    (hM : ∀ T : Set M.obj.V, T.Finite → ∃ (S : AddSubgroup M.obj.V)
      (hS : ∀ g : G, ∀ x ∈ S, (M.obj.ρ g).asHom.hom x ∈ S),
        T ⊆ S ∧ Subsingleton (H G (sub M S hS) 2)) :
    Subsingleton (H G M 2) := by
  classical
  rw [subsingleton_H_two_iff, forall_exists_comp_eq_iff]
  intro z hz
  obtain ⟨f, rfl⟩ := QuotientAddGroup.mk_surjective z
  have hrep := QuotientAddGroup.mk_surjective (s := toCoind₁Range M)
  let rep := Function.surjInv hrep
  have hT : (⋃ c ∈ Set.range f.1, Set.range (rep c).1).Finite :=
    (finite_range_smoothFunctions f).biUnion fun c _ ↦ finite_range_smoothFunctions (rep c)
  obtain ⟨S, hS, hTS, hS2⟩ := hM _ hT
  rw [subsingleton_H_two_iff, forall_exists_comp_eq_iff] at hS2
  let j := coker₁SubMap M S hS
  let Φ : (coker₁ M).obj.V → (coker₁ (sub M S hS)).obj.V := fun c ↦
    if h : ∀ y, (rep c).1 y ∈ S then QuotientAddGroup.mk (smoothFunctionsCodRestrict M S _ h)
    else 0
  have hΦ (c) (hc : c ∈ Set.range f.1) : j (Φ c) = c := by
    have h : ∀ y, (rep c).1 y ∈ S := fun y ↦ hTS (Set.mem_biUnion hc ⟨y, rfl⟩)
    simp only [Φ, dite_eq_left h, j, coker₁SubMap_mk, smoothFunctionsMap_codRestrict]
    exact Function.surjInv_eq hrep c
  let fN : ((coind₁ G).obj (coker₁ (sub M S hS)).obj.V).obj.V :=
    ⟨Φ ∘ f.1, Subgroup.isOpen_mono (H₁ := rightStab G f.1)
      (fun _ hg x ↦ by simp only [Function.comp_apply, hg x]) f.2⟩
  have hjf (x : G) : j (fN.1 x) = f.1 x := hΦ _ ⟨x, rfl⟩
  have hinv (g : G) : ∃ c, ∀ x, f.1 (x * g) - f.1 x = ((coker₁ M).obj.ρ x).asHom.hom c := by
    have := hz g
    rw [coker₁_ρ_mk, coker₁_mk_eq_mk_iff] at this
    exact this
  have hzN : ∀ g, ((coker₁ (coker₁ (sub M S hS))).obj.ρ g).asHom.hom (QuotientAddGroup.mk fN) =
      QuotientAddGroup.mk fN := by
    intro g
    rw [coker₁_ρ_mk, coker₁_mk_eq_mk_iff]
    obtain ⟨c, hc⟩ := hinv g
    refine ⟨fN.1 g - fN.1 1, fun x ↦ injective_coker₁SubMap M S hS ?_⟩
    rw [map_sub, coker₁SubMap_ρ, map_sub]
    change j (fN.1 (x * g)) - j (fN.1 x) = ((coker₁ M).obj.ρ x).asHom.hom (j (fN.1 g) - j (fN.1 1))
    have hc1 := hc 1
    rw [one_mul, ρ_one_apply] at hc1
    rw [hjf, hjf, hjf, hjf, hc x, hc1]
  obtain ⟨y, hy, hpy⟩ := hS2 _ hzN
  rw [coker₁π_apply, coker₁_mk_eq_mk_iff] at hpy
  obtain ⟨c, hc⟩ := hpy
  refine ⟨smoothFunctionsMap j y, fun g ↦ Subtype.ext (funext fun x ↦ ?_), ?_⟩
  · change j (y.1 (x * g)) = j (y.1 x)
    rw [show y.1 (x * g) = y.1 x from congr_fun (congrArg Subtype.val (hy g)) x]
  · rw [coker₁π_apply, coker₁_mk_eq_mk_iff]
    refine ⟨j c, fun x ↦ ?_⟩
    change j (y.1 x) - f.1 x = _
    rw [← hjf x, ← map_sub, hc x, coker₁SubMap_ρ]

end compact

lemma exists_pow_nsmul_eq_zero_of_finite (ℓ : ℕ) {A : Type*} [AddCommGroup A] {s : Set A}
    (hs : s.Finite) (h : ∀ a ∈ s, ∃ j : ℕ, ℓ ^ j • a = 0) :
    ∃ J : ℕ, ∀ a ∈ s, ℓ ^ J • a = 0 := by
  induction s, hs using Set.Finite.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert a s ha hs ih =>
    obtain ⟨J, hJ⟩ := ih fun b hb ↦ h b (Set.mem_insert_of_mem _ hb)
    obtain ⟨j, hj⟩ := h a (Set.mem_insert _ _)
    have key (b : A) (k : ℕ) (hk : k ≤ max j J) (hb : ℓ ^ k • b = 0) : ℓ ^ max j J • b = 0 :=
      addOrderOf_dvd_iff_nsmul_eq_zero.1
        ((addOrderOf_dvd_of_nsmul_eq_zero hb).trans (pow_dvd_pow ℓ hk))
    refine ⟨max j J, fun b hb ↦ ?_⟩
    rcases hb with rfl | hb
    · exact key b j (le_max_left _ _) hj
    · exact key b J (le_max_right _ _) (hJ b hb)

lemma isPrimary_quotient {ℓ : ℕ} {X : DiscreteModule.{w} G} (hX : IsPrimary ℓ X)
    (S : AddSubgroup X.obj.V) (hS : ∀ g : G, ∀ x ∈ S, (X.obj.ρ g).asHom.hom x ∈ S) :
    IsPrimary ℓ (quotient X S hS) := by
  intro q
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨j, hj⟩ := hX y
  exact ⟨j, by rw [← QuotientAddGroup.mk_nsmul, hj, QuotientAddGroup.mk_zero]⟩

lemma isPrimary_coker₁ [CompactSpace G] {ℓ : ℕ} {X : DiscreteModule.{w} G}
    (hX : IsPrimary ℓ X) : IsPrimary ℓ (coker₁ X) := by
  refine isPrimary_quotient (fun f ↦ ?_) _ _
  obtain ⟨J, hJ⟩ := exists_pow_nsmul_eq_zero_of_finite ℓ (finite_range_smoothFunctions f)
    (by rintro _ ⟨x, rfl⟩; exact hX _)
  exact ⟨J, Subtype.ext (funext fun x ↦ hJ _ ⟨x, rfl⟩)⟩

section main

variable [CompactSpace G] (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

/-- `H²(G, M) = 0` for a finite `ℓ`-primary module `M`, if `H²(K, 𝔽_ℓ) = 0` for every open
subgroup `K`: by restriction–corestriction to an open subgroup of index prime to `ℓ` acting on
`M` through an `ℓ`-group (`exists_isOpen_not_dvd_index_pow_mem`). -/
theorem subsingleton_H_two_of_finite
    (h2 : ∀ K : Subgroup G, IsOpen (K : Set G) → Subsingleton (H K (trivialZMod.{w} K ℓ) 2))
    (M : DiscreteModule.{w} G) [Finite M.obj.V] (hM : IsPrimary ℓ M) :
    Subsingleton (H G M 2) := by
  obtain ⟨K, hKo, hKℓ, -, hpow⟩ := exists_isOpen_not_dvd_index_pow_mem M ℓ
  have : K.FiniteIndex := ⟨fun h ↦ hKℓ (h ▸ dvd_zero ℓ)⟩
  have : Finite ((resSub K).obj M).obj.V := ‹Finite M.obj.V›
  have hK : Subsingleton (H K ((resSub K).obj M) 2) :=
    subsingleton_H_two_of_forall_pow_mem (G := K) ℓ ((actionKernel M).comap K.subtype)
      (fun k ↦ by simpa [Subgroup.mem_subgroupOf] using hpow k k.2) (h2 K hKo) _ _ rfl
      (fun k hk x ↦ (mem_actionKernel M).1 hk x) hM
  obtain ⟨J, hJ⟩ := exists_pow_nsmul_eq_zero_of_finite ℓ (Set.finite_univ (α := M.obj.V))
    fun a _ ↦ hM a
  have hcop : IsCoprime (K.index : ℤ) ((ℓ ^ J : ℕ) : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hℓ.out).2 hKℓ).symm
  obtain ⟨a, b, hab⟩ := hcop
  have key (x : H G M 2) : x = 0 := by
    have h1 := index_zsmul_eq_zero M hKo hK x
    have h2 : ((ℓ ^ J : ℕ) : ℤ) • x = 0 :=
      zsmul_eq_zero_of_forall_zsmul_eq_zero (fun m ↦ by
        rw [natCast_zsmul]; exact hJ m (Set.mem_univ _)) x
    calc x = (a * K.index + b * ((ℓ ^ J : ℕ) : ℤ)) • x := by rw [hab, one_smul]
      _ = 0 := by rw [add_smul, mul_smul, mul_smul, h1, h2, smul_zero, smul_zero, add_zero]
  exact ⟨fun x y ↦ by rw [key x, key y]⟩

/-- `H²(G, M) = 0` for every `ℓ`-primary module `M`, if `H²(K, 𝔽_ℓ) = 0` for every open
subgroup `K`: `M` is the union of its finite stable subgroups. -/
theorem subsingleton_H_two
    (h2 : ∀ K : Subgroup G, IsOpen (K : Set G) → Subsingleton (H K (trivialZMod.{w} K ℓ) 2))
    (M : DiscreteModule.{w} G) (hM : IsPrimary ℓ M) :
    Subsingleton (H G M 2) := by
  refine subsingleton_H_two_of_forall_finite M fun T hT ↦ ?_
  let U : Set M.obj.V := ⋃ t ∈ T, Set.range fun g : G ↦ (M.obj.ρ g).asHom.hom t
  have hU : U.Finite := hT.biUnion fun t _ ↦ finite_range_of_forall_mul_eq _
    (M.obj.stabilizer t) (M.isOpen_stabilizer t) fun x u hu ↦ by
      rw [ρ_mul_apply, mem_stabilizer.1 hu]
  have hstab : ∀ g : G, ∀ x ∈ AddSubgroup.closure U,
      (M.obj.ρ g).asHom.hom x ∈ AddSubgroup.closure U := by
    intro g x hx
    refine (AddSubgroup.closure_le (K := (AddSubgroup.closure U).comap (M.obj.ρ g).asHom.hom)).2
      ?_ hx
    intro u hu
    obtain ⟨t, ht, h, rfl⟩ : ∃ t ∈ T, ∃ h : G, (M.obj.ρ h).asHom.hom t = u := by simpa [U] using hu
    exact AddSubgroup.subset_closure (Set.mem_biUnion ht ⟨g * h, by simp⟩)
  refine ⟨_, hstab, fun t ht ↦ AddSubgroup.subset_closure (Set.mem_biUnion ht ⟨1, by simp⟩), ?_⟩
  have : Finite U := hU.to_subtype
  have : Finite (AddSubgroup.closure U) := AddCommGroup.finite_of_fg_isAddTorsion _ fun x ↦ by
    obtain ⟨j, hj⟩ := hM x.1
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨ℓ ^ j, pow_pos hℓ.out.pos j, Subtype.ext hj⟩
  have : Finite (sub M _ hstab).obj.V := this
  refine subsingleton_H_two_of_finite ℓ h2 _ fun x ↦ ?_
  obtain ⟨j, hj⟩ := hM x.1
  exact ⟨j, Subtype.ext hj⟩

/-- **A degree-two criterion for continuous cohomology.** Let `G` be a profinite (more
generally, compact) group and `ℓ` a prime such that `H²(K, 𝔽_ℓ) = 0` for every open subgroup
`K` of `G`. Then `Hⁿ(G, M) = 0` for every `n ≥ 2` and every discrete `ℓ`-primary `G`-module `M`.
(blueprint: `theorem-cohomology-curves`) -/
theorem subsingleton_H_of_two_le
    (h2 : ∀ K : Subgroup G, IsOpen (K : Set G) → Subsingleton (H K (trivialZMod.{w} K ℓ) 2))
    (M : DiscreteModule.{w} G) (hM : IsPrimary ℓ M) {n : ℕ} (hn : 2 ≤ n) :
    Subsingleton (H G M n) := by
  induction n, hn using Nat.le_induction generalizing M with
  | base => exact subsingleton_H_two ℓ h2 M hM
  | succ n hn ih =>
    exact subsingleton_ext_succ_of_shortExact (shortExact₁ M) (subsingleton_H_coind₁ _ n)
      (ih _ (isPrimary_coker₁ hM))

end main
end DiscreteModule
