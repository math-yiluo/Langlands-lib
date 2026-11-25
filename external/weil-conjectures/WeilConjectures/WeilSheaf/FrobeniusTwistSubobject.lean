/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Subobject.Lattice
public import WeilConjectures.WeilSheaf.StalkCharpoly
public import WeilConjectures.WeilSheaf.StalkFunctor
public import WeilConjectures.WeilSheaf.StalkFrobeniusPow
public import WeilConjectures.WeilSheaf.StalkTransportGeneral
public import WeilConjectures.WeilSheaf.LisseFiltration
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseIrreducible
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyIrreducible
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExists
public import WeilConjectures.SixFunctors.ProEtale.Adic.SubobjectStalk
public import WeilConjectures.RepresentationTheory.TwistedClifford
public import WeilConjectures.EtaleCohomology.Purity.RealSheaves.WeilFundamentalRepresentationStalk

/-!
# The Frobenius twist of subsheaves of a Weil sheaf

Let `F` be a Weil sheaf on a `k₀`-scheme `X`, with underlying `ℓ`-adic sheaf `F̄` on the geometric
fiber `X̄` and Weil structure `φ : Fr^* F̄ ≅ F̄`. A subsheaf `P ⊆ F̄` (a subobject in the category
of `ℓ`-adic sheaves, with no Weil structure) has a *Frobenius twist* `T P = φ (Fr^* P) ⊆ F̄`
(`AlgebraicGeometry.WeilSheaf.frobeniusTwist`); `T` is an order automorphism of the lattice of
subobjects of `F̄`, and its `n`-th iterate is `P ↦ φ_n ((Frⁿ)^* P)` for the iterated Weil
structure `φ_n` (`AlgebraicGeometry.WeilSheaf.frobeniusTwist_iterate_mk`).

The subsheaves fixed by `T` are the Weil subsheaves; those fixed by `T^N` are the subsheaves
defined over the extension of degree `N` of `k₀`: such a subsheaf carries the structure of an
algebra for the `N`-th Frobenius pullback (`AlgebraicGeometry.WeilSheaf.stableIsoAlgebra`),
compatibly with the iterated structure `φ_N` of `F` (`AlgebraicGeometry.WeilSheaf.powIsoAlgebra`).

This is the sheaf-theoretic side of the geometric constituents of a Weil sheaf (blueprint
`lemma-geometric-constituents-after-constant-extension--1`): an irreducible lisse Weil sheaf has a
geometrically irreducible subsheaf defined over a finite extension
(`AlgebraicGeometry.WeilSheaf.exists_isIrreducibleAdicLocalSystem_frobeniusTwist_iterate_eq`),
and its Frobenius conjugates span the whole sheaf
(`AlgebraicGeometry.WeilSheaf.iSup_frobeniusTwist_iterate_eq_top`).

On geometric stalks, the twist moves the stalk of `P` at `t ≫ Frᵃ` to the stalk of `Tᵃ P` at `t`
(`AlgebraicGeometry.WeilSheaf.stalkSubspace_frobeniusTwist_iterate`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

section Twist

variable (F : WeilSheaf k₀ l X)

/-- The *Frobenius twist* `P ↦ φ (Fr^* P)` of subobjects of the underlying `ℓ`-adic sheaf `F̄` of
a Weil sheaf, where `φ : Fr^* F̄ ≅ F̄` is the Weil structure: the transport of subobjects along
the autoequivalence `Fr^* = (Fr⁻¹)_*`, followed by `φ`. -/
noncomputable def frobeniusTwist : Subobject F.obj.carrier ≃o Subobject F.obj.carrier :=
  (Subobject.lowerEquivalence
      (MonoOver.congr F.obj.carrier (frobeniusPullback k₀ l X).asEquivalence)).toOrderIso.trans
    (Subobject.mapIsoToOrderIso F.obj.str)

/-- The Frobenius twist of the subobject given by a monomorphism `u : A ⟶ F̄` is given by the
monomorphism `φ ∘ Fr^* u`. -/
theorem frobeniusTwist_mk {A : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    (u : A ⟶ F.obj.carrier) [Mono u] :
    F.frobeniusTwist (Subobject.mk u) =
      Subobject.mk ((frobeniusPullback k₀ l X).map u ≫ F.obj.str.hom) := by
  exact Subobject.map_mk ((frobeniusPullback k₀ l X).map u) F.obj.str.hom

/-- The `n`-th iterate of the Frobenius twist of the subobject given by `u : A ⟶ F̄` is given by
the monomorphism `φ_n ∘ (Frⁿ)^* u`, for the iterated Weil structure `φ_n`
(`AlgebraicGeometry.WeilSheaf.frobeniusPowIso`). -/
theorem frobeniusTwist_iterate_mk {A : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    (u : A ⟶ F.obj.carrier) [Mono u] (n : ℕ) :
    (⇑F.frobeniusTwist)^[n] (Subobject.mk u) =
      Subobject.mk
        ((((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ n).asIso.inv)_*ᵃ[l].map u ≫
          (F.frobeniusPowIso n).hom) := by
  induction n with
  | zero =>
    refine (Subobject.mk_eq_mk_of_comm _ u
      ((adicLowerStarCongr l (by rw [pow_zero]; rfl)).app A ≪≫ (adicLowerStarId l _).app A)
      ?_).symm
    simp [frobeniusPowIso]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, frobeniusTwist_mk]
    refine Subobject.mk_eq_mk_of_comm _ _ ((adicLowerStarComp l
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ n).asIso.inv
      (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.asIso.inv).app A ≪≫
      (adicLowerStarCongr l (by rw [pow_succ]; rfl)).symm.app A) ?_
    simp [frobeniusPowIso]

/-- The underlying sheaf of the `n`-th iterate of the Frobenius twist of `P` is the `n`-th
Frobenius pullback `(Frⁿ)^* P = (Fr⁻ⁿ)_* P` of the underlying sheaf of `P`. -/
noncomputable def underlyingFrobeniusTwistIterateIso (P : Subobject F.obj.carrier) (n : ℕ) :
    Subobject.underlying.obj ((⇑F.frobeniusTwist)^[n] P) ≅
      (((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ n).asIso.inv)_*ᵃ[l].obj
        (Subobject.underlying.obj P) :=
  Subobject.isoOfEq _ _ ((congrArg (⇑F.frobeniusTwist)^[n] (Subobject.mk_arrow P)).symm.trans
    (F.frobeniusTwist_iterate_mk P.arrow n)) ≪≫ Subobject.underlyingIso _

/-- The Frobenius twist of a subsheaf which is an irreducible local system is an irreducible
local system: it is isomorphic to the pullback along the automorphism `Fr`. -/
theorem isIrreducibleAdicLocalSystem_frobeniusTwist_iterate {P : Subobject F.obj.carrier}
    (hP : IsIrreducibleAdicLocalSystem (Subobject.underlying.obj P)) (n : ℕ) :
    IsIrreducibleAdicLocalSystem (Subobject.underlying.obj ((⇑F.frobeniusTwist)^[n] P)) :=
  (hP.adicLowerStar_of_iso
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ n).asIso.symm).of_iso
      (F.underlyingFrobeniusTwistIterateIso P n).symm

/-- The Frobenius twist of a lisse subsheaf is lisse. -/
theorem isAdicLisseSheaf_frobeniusTwist_iterate {P : Subobject F.obj.carrier}
    (hP : IsAdicLisseSheaf (Subobject.underlying.obj P)) (n : ℕ) :
    IsAdicLisseSheaf (Subobject.underlying.obj ((⇑F.frobeniusTwist)^[n] P)) :=
  (hP.adicLowerStar_of_iso
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ n).asIso.symm).of_iso
      (F.underlyingFrobeniusTwistIterateIso P n).symm

end Twist

section IsoAlgebra

variable (F : WeilSheaf k₀ l X)

/-- The underlying `ℓ`-adic sheaf of a Weil sheaf with its iterated Weil structure
`φ_N : (Fr^N)^* F̄ ≅ F̄`, an algebra for the `N`-th Frobenius pullback. -/
noncomputable def powIsoAlgebra (N : ℕ) :
    IsoAlgebra ((((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.inv)_*ᵃ[l]) :=
  IsoAlgebra.mk F.obj.carrier (F.frobeniusPowIso N)

/-- A subsheaf `P ⊆ F̄` fixed by the `N`-th iterate of the Frobenius twist, with the structure of
an algebra for the `N`-th Frobenius pullback induced by `φ_N`: the isomorphism
`(Fr^N)^* P ≅ P` through which `φ_N ∘ (Fr^N)^* P.arrow` factors. -/
noncomputable def stableIsoAlgebra {N : ℕ} (P : Subobject F.obj.carrier)
    (hP : (⇑F.frobeniusTwist)^[N] P = P) :
    IsoAlgebra ((((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.inv)_*ᵃ[l]) :=
  IsoAlgebra.mk (Subobject.underlying.obj P)
    ((Subobject.underlyingIso _).symm ≪≫
      Subobject.isoOfEq _ _ ((F.frobeniusTwist_iterate_mk P.arrow N).symm.trans
        ((congrArg (⇑F.frobeniusTwist)^[N] (Subobject.mk_arrow P)).trans hP)))

/-- The inclusion `P ⟶ F̄` of a subsheaf fixed by the `N`-th iterate of the Frobenius twist is a
morphism of algebras for the `N`-th Frobenius pullback. -/
noncomputable def stableIsoAlgebraι {N : ℕ} (P : Subobject F.obj.carrier)
    (hP : (⇑F.frobeniusTwist)^[N] P = P) :
    F.stableIsoAlgebra P hP ⟶ F.powIsoAlgebra N :=
  ObjectProperty.homMk ⟨P.arrow, by
    simp [stableIsoAlgebra, powIsoAlgebra]⟩

@[simp]
lemma stableIsoAlgebraι_hom_f {N : ℕ} (P : Subobject F.obj.carrier)
    (hP : (⇑F.frobeniusTwist)^[N] P = P) :
    (F.stableIsoAlgebraι P hP).hom.f = P.arrow :=
  rfl

/-- A lisse subsheaf `P ⊆ F̄` fixed by the Frobenius twist underlies a lisse Weil subsheaf of
`F`. -/
theorem exists_mono_of_frobeniusTwist_eq {P : Subobject F.obj.carrier}
    (hP : F.frobeniusTwist P = P) (hPl : IsAdicLisseSheaf (Subobject.underlying.obj P)) :
    ∃ (G : WeilSheaf k₀ l X) (i : G ⟶ F), Mono i ∧ G.IsLisse ∧
      ∃ _ : Mono i.hom.hom.f, Subobject.mk i.hom.hom.f = P := by
  have e : Subobject.mk ((frobeniusPullback k₀ l X).map P.arrow ≫ F.obj.str.hom) = P :=
    (F.frobeniusTwist_mk P.arrow).symm.trans
      ((congrArg F.frobeniusTwist (Subobject.mk_arrow P)).trans hP)
  let str : (frobeniusPullback k₀ l X).obj (Subobject.underlying.obj P) ≅
      Subobject.underlying.obj P :=
    (Subobject.underlyingIso _).symm ≪≫ Subobject.isoOfEq _ _ e
  let G : WeilSheaf k₀ l X :=
    ⟨IsoAlgebra.mk (Subobject.underlying.obj P) str, hPl.isAdicConstructibleSheaf⟩
  have hc : (frobeniusPullback k₀ l X).map P.arrow ≫ F.obj.str.hom = str.hom ≫ P.arrow := by
    simp [str]
  let i : G ⟶ F := ObjectProperty.homMk (ObjectProperty.homMk ⟨P.arrow, hc⟩)
  have : Mono ((ObjectProperty.ι _ ⋙ IsoAlgebra.forget _).map i) :=
    inferInstanceAs (Mono P.arrow)
  exact ⟨G, i, (ObjectProperty.ι _ ⋙ IsoAlgebra.forget _).mono_of_mono_map this, hPl,
    inferInstanceAs (Mono P.arrow), Subobject.mk_arrow P⟩

end IsoAlgebra

section Stalk

variable (F : WeilSheaf k₀ l X)

/-- The geometric stalk `P_t ⊆ F_t` of a subsheaf `P ⊆ F̄` at a geometric point `t`: the image of
the stalk of `P` in the stalk of `F`. -/
noncomputable def stalkSubspace
    (t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (P : Subobject F.obj.carrier) :
    Submodule (PadicAlgCl l) ((WeilCoefficients.toModuleCat l).obj (F.stalkObj t)) :=
  LinearMap.range ((WeilCoefficients.toModuleCat l).map ((Sheaf.Γ _ _).map
    ((t)^*[WeilCoefficients.{u} l].map ((ProEtale.AdicSheaf.forget _).map P.arrow)))).hom

/-- The geometric stalk of a subsheaf of a Weil sheaf is that of the subsheaf of the underlying
`ℓ`-adic sheaf. -/
theorem stalkSubspace_eq_adicStalkSubspace
    (t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (P : Subobject F.obj.carrier) :
    F.stalkSubspace t P = adicStalkSubspace t P :=
  rfl

/-- The stalk of the whole sheaf is the whole stalk. -/
theorem stalkSubspace_top
    (t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    F.stalkSubspace t ⊤ = ⊤ :=
  adicStalkSubspace_top t _

/-- If finitely many subsheaves span `F̄`, their stalks span the stalk of `F`: the stalk functor
is exact. -/
theorem iSup_stalkSubspace_eq_top
    (t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    {M : ℕ} (Q : Fin M → Subobject F.obj.carrier) (hQ : (Finset.univ : Finset (Fin M)).sup Q = ⊤) :
    ⨆ n, F.stalkSubspace t (Q n) = ⊤ := by
  rw [← adicStalkSubspace_top t F.obj.carrier, ← hQ, adicStalkSubspace_finset_sup]
  simp [stalkSubspace_eq_adicStalkSubspace]

/-- The identification `A_{s ≫ e} ≅ (e^* A)_s ≅ ((e⁻¹)_* A)_s` of geometric stalks of an `ℓ`-adic
sheaf `A`, for an automorphism `e` of the geometric fiber. -/
noncomputable def stalkLowerStarInvIso
    (e : (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (A : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    (adicStalkFunctor l (s ≫ e.hom)).obj A ≅ (adicStalkFunctor l s).obj ((e.inv)_*ᵃ[l].obj A) :=
  (Sheaf.Γ _ _).mapIso ((ProEtale.upperStarComp _ s e.hom).app A.X ≪≫
    (s)^*[_].mapIso ((ProEtale.upperStarIsoLowerStarInv _ e).app A.X))

omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] in
/-- The identification `A_{s ≫ e} ≅ ((e⁻¹)_* A)_s` is natural in `A`. -/
lemma stalkLowerStarInvIso_hom_naturality
    (e : (X ↘ Spec (CommRingCat.of k₀)).geometricFiber ≅
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    {A B : AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber} (u : A ⟶ B) :
    (adicStalkFunctor l (s ≫ e.hom)).map u ≫ (stalkLowerStarInvIso e s B).hom =
      (stalkLowerStarInvIso e s A).hom ≫ (adicStalkFunctor l s).map ((e.inv)_*ᵃ[l].map u) := by
  simp only [stalkLowerStarInvIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Functor.comp_map, ← Functor.map_comp, Category.assoc]
  congr 1
  have n₁ := (ProEtale.upperStarComp (WeilCoefficients.{u} l) s e.hom).hom.naturality
    ((ProEtale.AdicSheaf.forget _).map u)
  have n₂ := (ProEtale.upperStarIsoLowerStarInv (WeilCoefficients.{u} l) e).hom.naturality
    ((ProEtale.AdicSheaf.forget _).map u)
  erw [reassoc_of% n₁]
  simp only [← Functor.map_comp]
  erw [n₂]
  rfl

/-- The isomorphism `F_{s ≫ Frᵐ} ≅ F_s` of the iterated Weil structure, through the
identification `F_{s ≫ Frᵐ} ≅ ((Fr⁻ᵐ)_* F)_s`. -/
lemma stalkObjFrobeniusPowIso_hom_eq_stalkLowerStarInvIso (m : ℕ)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) :
    (F.stalkObjFrobeniusPowIso m s).hom =
      (stalkLowerStarInvIso ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso s
        F.obj.carrier).hom ≫ (adicStalkFunctor l s).map (F.frobeniusPowIso m).hom := by
  simp only [stalkObjFrobeniusPowIso, stalkLowerStarInvIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Functor.comp_map, ← Functor.map_comp, Category.assoc]

/-- The stalk at `t` of the `a`-th Frobenius twist of `P` is the image of the stalk of `P` at
`t ≫ Frᵃ` under the identification `F_{t ≫ Frᵃ} ≅ F_t` induced by `φ_a`
(`AlgebraicGeometry.WeilSheaf.stalkObjFrobeniusPowIso`). -/
theorem stalkSubspace_frobeniusTwist_iterate
    (t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (P : Subobject F.obj.carrier) (a : ℕ) :
    F.stalkSubspace t ((⇑F.frobeniusTwist)^[a] P) =
      (F.stalkSubspace (t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).asIso.hom)
        P).map (WeilCoefficients.linearEquivOfIso (F.stalkObjFrobeniusPowIso a t)).toLinearMap := by
  set Fr := (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius
  have h : (WeilCoefficients.linearEquivOfIso (F.stalkObjFrobeniusPowIso a t)).toLinearMap ∘ₗ
      adicStalkMap (t ≫ (Fr ^ a).asIso.hom) P.arrow =
      adicStalkMap t ((((Fr ^ a).asIso.inv)_*ᵃ[l]).map P.arrow ≫ (F.frobeniusPowIso a).hom) ∘ₗ
        ((WeilCoefficients.toModuleCat l).map
          (stalkLowerStarInvIso (Fr ^ a).asIso t (Subobject.underlying.obj P)).hom).hom := by
    have n := stalkLowerStarInvIso_hom_naturality (Fr ^ a).asIso t P.arrow =≫
      (adicStalkFunctor l t).map (F.frobeniusPowIso a).hom
    simp only [Category.assoc, ← Functor.map_comp] at n
    rw [← stalkObjFrobeniusPowIso_hom_eq_stalkLowerStarInvIso] at n
    have n' := congrArg (fun f ↦ ((WeilCoefficients.toModuleCat l).map f).hom) n
    simp only [Functor.map_comp, ModuleCat.hom_comp] at n'
    rw [adicStalkMap_comp]
    exact n'.trans (LinearMap.comp_assoc _ _ _)
  conv_lhs => rw [← Subobject.mk_arrow P, frobeniusTwist_iterate_mk]
  rw [stalkSubspace_eq_adicStalkSubspace, stalkSubspace_eq_adicStalkSubspace, adicStalkSubspace_mk,
    adicStalkSubspace, ← LinearMap.range_comp, h, LinearMap.range_comp_of_range_eq_top]
  exact LinearMap.range_eq_top.2 ((WeilCoefficients.toModuleCat l).mapIso
    (stalkLowerStarInvIso (Fr ^ a).asIso t (Subobject.underlying.obj P))).toLinearEquiv.surjective

/-- The reparametrisation `F_{σᵃ ≫ t} ≅ F_t` of a geometric point by a power of the Frobenius
of `k̄` (`AlgebraicGeometry.WeilSheaf.stalkObjSpecFrobeniusPowIso`) carries the stalk of `P` at
`σᵃ ≫ t` to its stalk at `t`. -/
theorem stalkSubspace_specGeometricFrobenius_pow
    (t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (P : Subobject F.obj.carrier) (a : ℕ) :
    (F.stalkSubspace ((specGeometricFrobenius k₀ ^ a).asIso.hom ≫ t) P).map
        (WeilCoefficients.linearEquivOfIso (F.stalkObjSpecFrobeniusPowIso a t)).toLinearMap =
      F.stalkSubspace t P := by
  have h : (WeilCoefficients.linearEquivOfIso (F.stalkObjSpecFrobeniusPowIso a t)).toLinearMap ∘ₗ
      adicStalkMap ((specGeometricFrobenius k₀ ^ a).asIso.hom ≫ t) P.arrow =
      adicStalkMap t P.arrow ∘ₗ ((WeilCoefficients.toModuleCat l).map
        (reparamStalkIso l (specGeometricFrobenius k₀ ^ a).asIso t
          (Subobject.underlying.obj P).X).hom).hom := by
    have n := congrArg (fun f ↦ ((WeilCoefficients.toModuleCat l).map f).hom)
      (reparamStalkIso_hom_naturality (specGeometricFrobenius k₀ ^ a).asIso t
        ((ProEtale.AdicSheaf.forget _).map P.arrow))
    simp only [Functor.map_comp, ModuleCat.hom_comp] at n
    exact n
  rw [stalkSubspace_eq_adicStalkSubspace, stalkSubspace_eq_adicStalkSubspace, adicStalkSubspace,
    adicStalkSubspace, ← LinearMap.range_comp, h, LinearMap.range_comp_of_range_eq_top]
  exact LinearMap.range_eq_top.2 ((WeilCoefficients.toModuleCat l).mapIso
    (reparamStalkIso l (specGeometricFrobenius k₀ ^ a).asIso t
      (Subobject.underlying.obj P).X)).toLinearEquiv.surjective

/-- The identification of stalks at equal geometric points carries the stalk of a subsheaf to
its stalk. -/
theorem stalkSubspace_map_eqToIso {s s' : Spec (.of (AlgebraicClosure k₀)) ⟶
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber} (h : s = s') (P : Subobject F.obj.carrier) :
    (F.stalkSubspace s P).map
        (WeilCoefficients.linearEquivOfIso (eqToIso (congrArg F.stalkObj h))).toLinearMap =
      F.stalkSubspace s' P := by
  subst h
  ext v
  simp [WeilCoefficients.linearEquivOfIso]

/-- The stalk at a geometric point `t` fixed by `Frᴺ` up to reparametrisation of the `N`-th
Frobenius twist of `P` is the image of the stalk of `P` under the Frobenius relative to
`𝔽_{qᴺ}`. -/
theorem stalkSubspace_frobeniusTwist_iterate_eq_map_frobenius
    {t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {N : ℕ} (ht : t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom =
      (specGeometricFrobenius k₀ ^ N).asIso.hom ≫ t)
    (P : Subobject F.obj.carrier) :
    F.stalkSubspace t ((⇑F.frobeniusTwist)^[N] P) =
      (F.stalkSubspace t P).map (F.stalkAt t N ht).frobenius.toLinearMap := by
  have hρ : (F.stalkSubspace t P).map
      (WeilCoefficients.linearEquivOfIso (F.stalkObjSpecFrobeniusPowIso N t)).symm.toLinearMap =
      F.stalkSubspace ((specGeometricFrobenius k₀ ^ N).asIso.hom ≫ t) P :=
    (Submodule.map_symm_eq_iff _).2 (F.stalkSubspace_specGeometricFrobenius_pow t P N)
  rw [stalkAt_frobenius_eq, WeilCoefficients.linearEquivOfIso_trans,
    WeilCoefficients.linearEquivOfIso_trans, WeilCoefficients.linearEquivOfIso_symm,
    LinearEquiv.coe_trans, LinearEquiv.coe_trans, Submodule.map_comp, Submodule.map_comp, hρ,
    stalkSubspace_map_eqToIso _ ht.symm, stalkSubspace_frobeniusTwist_iterate]

/-- The stalk at a geometric point `t` fixed by `Frᴺ` up to reparametrisation of the `Ni`-th
Frobenius twist of `P` is the image of the stalk of `P` under the `i`-th power of the Frobenius
relative to `𝔽_{qᴺ}`. -/
theorem stalkSubspace_frobeniusTwist_iterate_mul_eq_map_pow
    {t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {N : ℕ} (ht : t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom =
      (specGeometricFrobenius k₀ ^ N).asIso.hom ≫ t)
    (P : Subobject F.obj.carrier) (i : ℕ) :
    F.stalkSubspace t ((⇑F.frobeniusTwist)^[N * i] P) =
      (F.stalkSubspace t P).map ((F.stalkAt t N ht).frobenius.toLinearMap ^ i) := by
  induction i with
  | zero =>
    rw [Nat.mul_zero, Function.iterate_zero_apply, pow_zero, Module.End.one_eq_id,
      Submodule.map_id]
  | succ i ih =>
    rw [Nat.mul_succ, Nat.add_comm, Function.iterate_add_apply,
      F.stalkSubspace_frobeniusTwist_iterate_eq_map_frobenius ht, ih, ← Submodule.map_comp,
      pow_succ']
    rfl

/-- The stalk at `t` of a subsheaf fixed by `T^N` is stable under the Frobenius relative to
`𝔽_{q^N}` of the stalk of `F` at a geometric point `t` fixed by `Fr^N` up to reparametrisation. -/
theorem frobenius_mem_stalkSubspace
    {t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {N : ℕ} (ht : t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom =
      (specGeometricFrobenius k₀ ^ N).asIso.hom ≫ t)
    {P : Subobject F.obj.carrier} (hP : (⇑F.frobeniusTwist)^[N] P = P)
    {v : (F.stalkAt t N ht).carrier} (hv : v ∈ F.stalkSubspace t P) :
    (F.stalkAt t N ht).frobenius v ∈ F.stalkSubspace t P := by
  rw [← hP, F.stalkSubspace_frobeniusTwist_iterate_eq_map_frobenius ht P]
  exact Submodule.mem_map_of_mem hv

/-- The isomorphism `F_{s ≫ Frᵃ} ≅ F_s` of the iterated Weil structure is the transport along the
square `𝟙 ≫ (s ≫ Frᵃ) = s ≫ Frᵃ`. -/
lemma stalkObjFrobeniusPowIso_hom_eq_globalSectionsTransport (a : ℕ)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (h : 𝟙 _ ≫ s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).asIso.hom =
      s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).asIso.hom) :
    (F.stalkObjFrobeniusPowIso a s).hom =
      ProEtale.globalSectionsTransport _ h (F.frobeniusPowStr a) := by
  have e₀ := ProEtale.upperStarComp_id_left_hom_app (WeilCoefficients.{u} l)
    (s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).asIso.hom) F.obj.carrier.X
  have e : (ProEtale.upperStarId (WeilCoefficients.{u} l) _).inv.app _ ≫
      (ProEtale.upperStarComp (WeilCoefficients.{u} l) (𝟙 _)
        (s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).asIso.hom)).inv.app
          F.obj.carrier.X =
      (ProEtale.upperStarCongr (WeilCoefficients.{u} l) (Category.id_comp _)).inv.app
        F.obj.carrier.X := by
    rw [← cancel_epi ((ProEtale.upperStarCongr (WeilCoefficients.{u} l)
      (Category.id_comp _)).hom.app F.obj.carrier.X), Iso.hom_inv_id_app, ← e₀]
    simp
  rw [ProEtale.globalSectionsTransport, ProEtale.globalSectionsToUpperStar_id_app,
    ProEtale.upperStarCompIso_hom_app, ← Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% e]
  simp only [stalkObjFrobeniusPowIso, Functor.comp_obj, Functor.mapIso_trans, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Mod.forget_map, Functor.id_obj, ProEtale.upperStarCongr,
    eqToIso_refl, Iso.refl_inv, NatTrans.id_app, Iso.refl_hom, frobeniusPowStr, Functor.map_comp,
    Category.id_comp]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- The Frobenius transports at two geometric points `s` and `s'` related by a square
`g ≫ s = s' ≫ Frʲ`, with `g` commuting with `σ`, are intertwined by the transport along that
square (for all `j` and `m`). -/
lemma globalSectionsTransport_frobeniusPowStr_comm' {s s' : Spec (.of (AlgebraicClosure k₀)) ⟶
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber} {g σ : Spec (.of (AlgebraicClosure k₀)) ⟶
      Spec (.of (AlgebraicClosure k₀))} (j m : ℕ)
    (hg : g ≫ s = s' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ j).asIso.hom)
    (hs : σ ≫ s = s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom)
    (hs' : σ ≫ s' = s' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom)
    (hcomm : g ≫ σ = σ ≫ g) :
    ProEtale.globalSectionsTransport _ hs (F.frobeniusPowStr m) ≫
        ProEtale.globalSectionsTransport _ hg (F.frobeniusPowStr j) =
      ProEtale.globalSectionsTransport _ hg (F.frobeniusPowStr j) ≫
        ProEtale.globalSectionsTransport _ hs' (F.frobeniusPowStr m) := by
  have h₁ : (g ≫ σ) ≫ s = s' ≫
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (m + j)).asIso.hom := by
    rw [Category.assoc, hs, ← Category.assoc, hg, Category.assoc,
      CategoryTheory.Aut.pow_hom_comp_pow_hom]
  have h₂ : (σ ≫ g) ≫ s = s' ≫
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (j + m)).asIso.hom := by
    rw [Category.assoc, hg, ← Category.assoc, hs', Category.assoc,
      CategoryTheory.Aut.pow_hom_comp_pow_hom]
  rw [F.globalSectionsTransport_frobeniusPowStr_comp' m j hs hg rfl h₁,
    F.globalSectionsTransport_frobeniusPowStr_comp' j m hg hs' rfl h₂]
  exact F.globalSectionsTransport_frobeniusPowStr_congr (Nat.add_comm m j) hcomm h₁ h₂

/-- The Frobenius of the stalk at `s` relative to `𝔽_{qᵐ}` (the definition, stated separately so
that the kernel checks the unfolding in isolation). -/
private lemma stalkAt_frobenius_eq_linearEquivOfIso
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) (m : ℕ)
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) :
    (F.stalkAt s m hs).frobenius = WeilCoefficients.linearEquivOfIso
      ((F.stalkObjSpecFrobeniusPowIso m s).symm ≪≫ eqToIso (congrArg F.stalkObj hs.symm) ≪≫
        F.stalkObjFrobeniusPowIso m s) :=
  rfl

/-- The Frobenius of the stalk at `s` relative to `𝔽_{qᵐ}`, applied to a vector. -/
private lemma stalkAt_frobenius_apply_eq_toModuleCat_map
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) (m : ℕ)
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) (x : (F.stalkAt s m hs).carrier) :
    (F.stalkAt s m hs).frobenius x = ((WeilCoefficients.toModuleCat l).map
      ((F.stalkObjSpecFrobeniusPowIso m s).symm ≪≫ eqToIso (congrArg F.stalkObj hs.symm) ≪≫
        F.stalkObjFrobeniusPowIso m s).hom).hom x :=
  (LinearEquiv.congr_fun (F.stalkAt_frobenius_eq_linearEquivOfIso s m hs) x).trans
    (WeilCoefficients.linearEquivOfIso_apply_eq_toModuleCat_map _ x)

/-- A morphism of stalks `F_s ⟶ F_{s'}` which is the transport along a square `g ≫ s = s' ≫ Frʲ`
intertwines the Frobenius relative to `𝔽_{qᵐ}`. -/
lemma toModuleCat_map_frobenius_stalkAt_of_eq
    {s s' : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {g : Spec (.of (AlgebraicClosure k₀)) ⟶ Spec (.of (AlgebraicClosure k₀))} {j m : ℕ}
    (hg : g ≫ s = s' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ j).asIso.hom)
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s)
    (hs' : s' ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s')
    (hcomm : g ≫ (specGeometricFrobenius k₀ ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ g)
    (f : F.stalkObj s ⟶ F.stalkObj s')
    (hf : f = ProEtale.globalSectionsTransport _ hg (F.frobeniusPowStr j))
    (v : (F.stalkAt s m hs).carrier) :
    ((WeilCoefficients.toModuleCat l).map f).hom ((F.stalkAt s m hs).frobenius v) =
      (F.stalkAt s' m hs').frobenius (((WeilCoefficients.toModuleCat l).map f).hom v) := by
  have hA : ((F.stalkObjSpecFrobeniusPowIso m s).symm ≪≫ eqToIso (congrArg F.stalkObj hs.symm) ≪≫
      F.stalkObjFrobeniusPowIso m s).hom ≫ f = f ≫
      ((F.stalkObjSpecFrobeniusPowIso m s').symm ≪≫ eqToIso (congrArg F.stalkObj hs'.symm) ≪≫
        F.stalkObjFrobeniusPowIso m s').hom := by
    rw [F.stalkAt_frobenius_hom_eq_globalSectionsTransport s m hs,
      F.stalkAt_frobenius_hom_eq_globalSectionsTransport s' m hs', hf]
    exact F.globalSectionsTransport_frobeniusPowStr_comm' j m hg hs.symm hs'.symm hcomm
  have hB := congrArg (fun φ ↦ ((WeilCoefficients.toModuleCat l).map φ).hom v) hA
  simp only [Functor.map_comp, ModuleCat.hom_comp] at hB
  exact (congrArg _ (F.stalkAt_frobenius_apply_eq_toModuleCat_map s m hs v)).trans
    (hB.trans (F.stalkAt_frobenius_apply_eq_toModuleCat_map s' m hs' _).symm)

/-- The inverse of the reparametrisation `F_{σᵃ ≫ s} ≅ F_s` is the transport along the square
`σᵃ ≫ s = (σᵃ ≫ s) ≫ Fr⁰` and the `0`-th iterate of the Weil structure. -/
lemma stalkObjSpecFrobeniusPowIso_inv_eq_globalSectionsTransport (a : ℕ)
    (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (h : (specGeometricFrobenius k₀ ^ a).asIso.hom ≫ s =
      ((specGeometricFrobenius k₀ ^ a).asIso.hom ≫ s) ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).asIso.hom) :
    (F.stalkObjSpecFrobeniusPowIso a s).inv =
      ProEtale.globalSectionsTransport _ h (F.frobeniusPowStr 0) := by
  have p : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).asIso.hom = 𝟙 _ := by
    rw [pow_zero]
    rfl
  rw [ProEtale.globalSectionsTransport_congr _ h p _ _ (F.frobeniusPowStr_zero p),
    ProEtale.globalSectionsTransport_eq_of_iso _ (specGeometricFrobenius k₀ ^ a).asIso,
    ProEtale.upperStarCompIso_hom_app, Category.assoc, Category.assoc,
    ProEtale.upperStarComp_id_right_hom_app,
    ProEtale.upperStarCongr_hom_app_comp_hom_app _ _ _ rfl]
  simp [stalkObjSpecFrobeniusPowIso, ProEtale.upperStarCongr]

/-- The identification `F_{t ≫ Frᵃ} ≅ F_t` induced by `φ_a` intertwines the Frobenius relative to
`𝔽_{q^N}` at the two geometric points. -/
theorem stalkObjFrobeniusPowIso_frobenius
    {t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {N : ℕ} (ht : t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom =
      (specGeometricFrobenius k₀ ^ N).asIso.hom ≫ t) (a : ℕ)
    (ht' : (t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).asIso.hom) ≫
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom =
        (specGeometricFrobenius k₀ ^ N).asIso.hom ≫
          t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).asIso.hom)
    (v : (F.stalkAt _ N ht').carrier) :
    WeilCoefficients.linearEquivOfIso (F.stalkObjFrobeniusPowIso a t)
        ((F.stalkAt _ N ht').frobenius v) =
      (F.stalkAt t N ht).frobenius
        (WeilCoefficients.linearEquivOfIso (F.stalkObjFrobeniusPowIso a t) v) :=
  (WeilCoefficients.linearEquivOfIso_apply_eq_toModuleCat_map _ _).trans
    ((F.toModuleCat_map_frobenius_stalkAt_of_eq
      (s := t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ a).asIso.hom) (s' := t)
      (Category.id_comp _) ht' ht (by simp) _
      (F.stalkObjFrobeniusPowIso_hom_eq_globalSectionsTransport a t (Category.id_comp _)) v).trans
        (congrArg _ (WeilCoefficients.linearEquivOfIso_apply_eq_toModuleCat_map _ v).symm))

/-- The reparametrisation `F_{σᵃ ≫ t} ≅ F_t` intertwines the Frobenius relative to `𝔽_{q^N}`. -/
theorem stalkObjSpecFrobeniusPowIso_frobenius
    {t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {N : ℕ} (ht : t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom =
      (specGeometricFrobenius k₀ ^ N).asIso.hom ≫ t) (a : ℕ)
    (ht' : ((specGeometricFrobenius k₀ ^ a).asIso.hom ≫ t) ≫
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ N).asIso.hom =
        (specGeometricFrobenius k₀ ^ N).asIso.hom ≫ (specGeometricFrobenius k₀ ^ a).asIso.hom ≫ t)
    (v : (F.stalkAt _ N ht').carrier) :
    WeilCoefficients.linearEquivOfIso (F.stalkObjSpecFrobeniusPowIso a t)
        ((F.stalkAt _ N ht').frobenius v) =
      (F.stalkAt t N ht).frobenius
        (WeilCoefficients.linearEquivOfIso (F.stalkObjSpecFrobeniusPowIso a t) v) := by
  have h₀ : (specGeometricFrobenius k₀ ^ a).asIso.hom ≫ t =
      ((specGeometricFrobenius k₀ ^ a).asIso.hom ≫ t) ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).asIso.hom := by
    rw [pow_zero]
    exact (Category.comp_id _).symm
  have hcomm :
      (specGeometricFrobenius k₀ ^ a).asIso.hom ≫ (specGeometricFrobenius k₀ ^ N).asIso.hom =
      (specGeometricFrobenius k₀ ^ N).asIso.hom ≫ (specGeometricFrobenius k₀ ^ a).asIso.hom := by
    rw [CategoryTheory.Aut.pow_hom_comp_pow_hom, CategoryTheory.Aut.pow_hom_comp_pow_hom,
      Nat.add_comm]
  have key := F.toModuleCat_map_frobenius_stalkAt_of_eq h₀ ht ht' hcomm _
    (F.stalkObjSpecFrobeniusPowIso_inv_eq_globalSectionsTransport a t h₀)
    (WeilCoefficients.linearEquivOfIso (F.stalkObjSpecFrobeniusPowIso a t) v)
  apply (WeilCoefficients.linearEquivOfIso (F.stalkObjSpecFrobeniusPowIso a t)).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  have hv :=
    (WeilCoefficients.linearEquivOfIso (F.stalkObjSpecFrobeniusPowIso a t)).symm_apply_apply v
  exact (key.trans (congrArg _ hv)).symm

/-- A subsheaf which is an irreducible local system has a nonzero stalk at every geometric point,
when the geometric fiber is connected, regular and locally Noetherian. -/
theorem stalkSubspace_ne_bot
    [ConnectedSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    [IsRegular (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    [IsLocallyNoetherian (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    [CompactSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    (t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    {P : Subobject F.obj.carrier}
    (hP : IsIrreducibleAdicLocalSystem (Subobject.underlying.obj P)) :
    F.stalkSubspace t P ≠ ⊥ := by
  intro h
  obtain ⟨M, hM⟩ := exists_lisseMonodromy (l := l)
    (Y := (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
    (Ω := k₀)
  have : Subsingleton (LisseMonodromy.StalkSpace t
      (⟨Subobject.underlying.obj P, hP.1⟩ : LisseSheaf l _)) := by
    refine ⟨fun v w ↦ injective_adicStalkMap t P.arrow ?_⟩
    have hv : adicStalkMap t P.arrow v ∈ F.stalkSubspace t P := LinearMap.mem_range_self _ v
    have hw : adicStalkMap t P.arrow w ∈ F.stalkSubspace t P := LinearMap.mem_range_self _ w
    rw [h, Submodule.mem_bot] at hv hw
    rw [hv, hw]
  exact hP.2.1 ((hM t).isZero_of_subsingleton ⟨Subobject.underlying.obj P, hP.1⟩)

end Stalk

section Monodromy

open Scheme.FiniteEtale

variable (F : WeilSheaf k₀ l X)

/-- The loop `F_t ≅ F_s ≅ F_{σᵐ ≫ s} = F_{s ≫ Frᵐ} ≅ F_{t ≫ Frᵐ}` at a geometric point `s` with
`s ≫ Frᵐ = σᵐ ≫ s`, for a path `π : F_s ≅ F_t`. -/
noncomputable def frobeniusPathOfPath
    {s t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {m : ℕ} (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) (π : fiber s ≅ fiber t) :
    fiber t ≅ fiber (t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom) :=
  π.symm ≪≫ (fiberReparamIso (specGeometricFrobenius k₀ ^ m).asIso s).symm ≪≫
    eqToIso (congrArg fiber hs.symm) ≪≫
    pullbackPathIso ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom π

/-- Transport along a path `π : F_s ≅ F_t` carries the Frobenius of the stalk at a geometric point
`s` with `s ≫ Frᵐ = σᵐ ≫ s` to the transport along the loop `frobeniusPathOfPath`, followed by
`F_{t ≫ Frᵐ} = ((Frᵐ)^* F)_t` and the stalk of `φ_m`. -/
theorem monoLinear_stalkAt_frobenius_eq
    (M : LisseMonodromy l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber k₀) (hF : F.IsLisse)
    {s t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {m : ℕ} (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ s) (π : fiber s ≅ fiber t)
    (v : (F.stalkAt s m hs).carrier) :
    M.monoLinear π (F.toLisse hF) ((F.stalkAt s m hs).frobenius v) =
      ((WeilCoefficients.toModuleCat l).map ((lisseStalk l t).map
        (F.lisseFrobPowStr hF m).hom)).hom
        (((WeilCoefficients.toModuleCat l).map (upperStarStalkIso l
          ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom t
            (F.toLisse hF).obj.X).hom).hom
          (M.monoLinear (frobeniusPathOfPath hs π) (F.toLisse hF)
            (M.monoLinear π (F.toLisse hF) v))) := by
  rw [WeilGroup.stalkAt_frobenius_apply F hF, ← M.reparam_upperStar_apply _
    (specGeometricFrobenius k₀ ^ m).asIso hs (F.toLisse hF) (F.lisseFrobPowStr hF m).hom v,
    M.reparam_comp_upperStar_comp_mono_apply _ _ hs π (F.toLisse hF)
      (F.lisseFrobPowStr hF m).hom v]
  rfl

/-- **The Frobenius twists the monodromy.** At a geometric point `t` with `t ≫ Frᵐ = σᵐ ≫ t`,
for every `g ∈ π₁(X̄, t)` there is `g'` with `ρ(g) ∘ Fₜ = Fₜ ∘ ρ(g')`, where `Fₜ` is the Frobenius
of the stalk relative to `𝔽_{qᵐ}`. -/
theorem exists_rep_stalkAt_frobenius
    (M : LisseMonodromy l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber k₀) (hF : F.IsLisse)
    {t : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber}
    {m : ℕ} (ht : t ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom =
      (specGeometricFrobenius k₀ ^ m).asIso.hom ≫ t) (g : Aut (fiber t)) :
    ∃ g' : Aut (fiber t), ∀ v : (F.stalkAt t m ht).carrier,
      M.rep t (F.toLisse hF) g ((F.stalkAt t m ht).frobenius v) =
        (F.stalkAt t m ht).frobenius (M.rep t (F.toLisse hF) g' v) := by
  let h : fiber t ≅ fiber t :=
    frobeniusPathOfPath ht g.asIso ≪≫ (frobeniusPathOfPath ht (Iso.refl _)).symm
  have hh : frobeniusPathOfPath ht g.asIso = h ≪≫ frobeniusPathOfPath ht (Iso.refl _) := by
    simp [h]
  have h₁ (w : (F.stalkAt t m ht).carrier) := F.monoLinear_stalkAt_frobenius_eq M hF ht
    (Iso.refl _) w
  refine ⟨Aut.of (g.asIso ≪≫ h), fun v ↦ ?_⟩
  rw [LisseMonodromy.rep_apply, LisseMonodromy.rep_apply, F.monoLinear_stalkAt_frobenius_eq M hF,
    hh, M.monoLinear_trans, ← M.monoLinear_refl t (F.toLisse hF)
      ((F.stalkAt t m ht).frobenius _), h₁, M.monoLinear_refl, M.monoLinear_trans,
    M.monoLinear_trans, M.monoLinear_trans]

end Monodromy

section Constituents

variable (F : WeilSheaf k₀ l X)

/-- **Geometric constituents** (blueprint:
`lemma-geometric-constituents-after-constant-extension--1`, sheaf form). A nonzero lisse Weil sheaf
`F` on `X`, with `X̄` connected, regular and locally Noetherian, has a subsheaf `P ⊆ F̄` which is an
irreducible local system and is fixed by some positive iterate of the Frobenius twist, i.e. is
defined over a finite extension of `k₀`. -/
theorem exists_isIrreducibleAdicLocalSystem_frobeniusTwist_iterate_eq
    [ConnectedSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    [IsRegular (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    [IsLocallyNoetherian (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    [CompactSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (hF : F.IsLisse) (hF0 : ¬ IsZero F) :
    ∃ P : Subobject F.obj.carrier, IsIrreducibleAdicLocalSystem (Subobject.underlying.obj P) ∧
      ∃ N : ℕ, 0 < N ∧ (⇑F.frobeniusTwist)^[N] P = P := by
  obtain ⟨x, hx⟩ := F.exists_nontrivial_stalk_of_not_isZero hF0
  have ht := Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow
    (X ↘ Spec (CommRingCat.of k₀)) x
  set t := (X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x
  set m := (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1
  have hm : 0 < m := Nat.pos_of_ne_zero ((X ↘ Spec (CommRingCat.of k₀)).degreeOver_ne_zero x.2)
  obtain ⟨M, hM⟩ := exists_lisseMonodromy (l := l)
    (Y := (X ↘ Spec (CommRingCat.of k₀)).geometricFiber) (Ω := k₀)
  have : Nontrivial (LisseMonodromy.StalkSpace t (F.toLisse hF)) := hx
  obtain ⟨j, hj, C, hC0, hCρ, hCirr, hCΘ⟩ :=
    Representation.exists_isIrreducible_pow_apply_mem_of_twist (M.rep t (F.toLisse hF))
      (F.stalkAt t m ht).frobenius (F.exists_rep_stalkAt_frobenius M hF ht)
  obtain ⟨P, hPl, hPC⟩ := exists_adicStalkSubspace_eq (hM t) hF C hCρ
  refine ⟨P, isIrreducibleAdicLocalSystem_of_adicStalkSubspace (hM t) hF hPl (hPC ▸ hC0)
    fun D hD hDle ↦ hPC ▸ hCirr D hD (hPC ▸ hDle), m * j, Nat.mul_pos hm hj, ?_⟩
  have hTP := F.stalkSubspace_frobeniusTwist_iterate_mul_eq_map_pow ht P j
  rw [stalkSubspace_eq_adicStalkSubspace, stalkSubspace_eq_adicStalkSubspace, hPC] at hTP
  have hle : C.map ((F.stalkAt t m ht).frobenius.toLinearMap ^ j) ≤ C :=
    Submodule.map_le_iff_le_comap.2 fun v hv ↦ hCΘ v hv
  have hinj : Function.Injective ((F.stalkAt t m ht).frobenius.toLinearMap ^ j) := by
    rw [Module.End.coe_pow]
    exact (F.stalkAt t m ht).frobenius.injective.iterate j
  have hCeq : C.map ((F.stalkAt t m ht).frobenius.toLinearMap ^ j) = C :=
    Submodule.eq_of_le_of_finrank_eq hle
      ((Submodule.equivMapOfInjective _ hinj C).finrank_eq.symm)
  have hTl := F.isAdicLisseSheaf_frobeniusTwist_iterate hPl (m * j)
  refine le_antisymm (le_of_adicStalkSubspace_le (hM t) hF hTl hPl ?_)
    (le_of_adicStalkSubspace_le (hM t) hF hPl hTl ?_)
  · rw [hTP, hCeq, hPC]
  · rw [hTP, hCeq, hPC]

/-- **The Frobenius conjugates of a geometric constituent span** (blueprint:
`theorem-real-constructible-sheaves-are-mixed--1`, descent of the constant extension). Let `F` be an
irreducible lisse Weil sheaf and `P ⊆ F̄` a nonzero lisse subsheaf fixed by `T^M`, `M > 0`, for the
Frobenius twist `T`. Then `P, T P, …, T^{M-1} P` span `F̄`: their sum is fixed by `T`, hence
underlies a nonzero lisse Weil subsheaf of `F`, which is `F`. -/
theorem iSup_frobeniusTwist_iterate_eq_top
    [IsLocallyNoetherian (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    (hF : F.IsIrreducibleLisse) {P : Subobject F.obj.carrier}
    (hPl : IsAdicLisseSheaf (Subobject.underlying.obj P)) (hP0 : P ≠ ⊥) {M : ℕ} (hM : 0 < M)
    (hP : (⇑F.frobeniusTwist)^[M] P = P) :
    (Finset.univ : Finset (Fin M)).sup (fun n ↦ (⇑F.frobeniusTwist)^[n] P) = ⊤ := by
  set T := F.frobeniusTwist
  set S := (Finset.univ : Finset (Fin M)).sup (fun n ↦ (⇑T)^[n] P)
  have hle (n : ℕ) : (⇑T)^[n] P ≤ S := by
    rw [← Nat.mod_add_div n M, Function.iterate_add_apply, Function.iterate_mul,
      Function.iterate_fixed hP]
    exact Finset.le_sup (f := fun n : Fin M ↦ (⇑T)^[n] P) (Finset.mem_univ ⟨n % M, n.mod_lt hM⟩)
  have hTS : T S = S := by
    refine le_antisymm ?_ ?_
    · rw [← OrderIso.le_symm_apply]
      refine Finset.sup_le fun n _ ↦ ?_
      rw [OrderIso.le_symm_apply, ← Function.iterate_succ_apply' (⇑T)]
      exact hle _
    · refine Finset.sup_le fun n _ ↦ ?_
      have h : (⇑T)^[n] P = T ((⇑T)^[n + M - 1] P) := by
        rw [← Function.iterate_succ_apply' (⇑T), Nat.succ_eq_add_one,
          Nat.sub_add_cancel (by omega), Function.iterate_add_apply, hP]
      rw [h]
      exact T.monotone (hle _)
  have hSl : IsAdicLisseSheaf (Subobject.underlying.obj S) :=
    IsAdicLisseSheaf.underlying_finset_sup hF.1 _ fun n _ ↦
      F.isAdicLisseSheaf_frobeniusTwist_iterate hPl n
  obtain ⟨G, i, hi, hG, hif, hS⟩ := F.exists_mono_of_frobeniusTwist_eq hTS hSl
  rcases hF.2.2 G i hi hG with h | h
  · refine absurd (eq_bot_iff.2 ((hle 0).trans_eq ?_)) hP0
    rw [← hS, Subobject.mk_eq_bot_iff_zero]
    exact (isZero_iff_isZero_carrier.1 h).eq_of_src _ _
  · have : IsIso i.hom.hom.f :=
      inferInstanceAs (IsIso ((ObjectProperty.ι _ ⋙ IsoAlgebra.forget _).map i))
    rw [← hS]
    exact Subobject.mk_eq_top_of_isIso _

end Constituents
end AlgebraicGeometry.WeilSheaf
