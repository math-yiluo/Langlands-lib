/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseGaloisDescent
public import WeilConjectures.WeilSheaf.StalkStrictlyHenselian

/-!
# Boundary stalks of direct images as Galois invariants

Let `j : U₀ ⟶ C₀` be a quasi-compact open immersion of `k₀`-schemes, `F` a lisse Weil sheaf on
`U₀` and `x` a closed point of `C₀` with geometric point `x̄`. Suppose given a strictly henselian
pro-étale neighbourhood `h : Spec A ⟶ C̄` of `x̄` whose punctured part `Spec A ×_C̄ Ū` is the
spectrum of a field `K'`, and a Galois extension `Ω / K'` (for a boundary point of a curve: the
strict henselization, the fraction field of the strict henselization and a separable closure,
so that `Gal(Ω / K')` is the inertia group at `x`). Then restriction of germs gives an injective
`ℚ̄_ℓ`-linear map `(j_* F)_x̄ ⟶ F(Spec Ω)` whose image is the module of `Gal(Ω / K')`-invariants
(`AlgebraicGeometry.WeilSheaf.exists_injective_stalk_directImage_range_eq_invariants`).

This combines the computation of stalks over strictly henselian neighbourhoods
(`AlgebraicGeometry.WeilSheaf.bijective_germ_stalk_directImage`) with Galois descent for
sections of lisse sheaves over fields
(`AlgebraicGeometry.ProEtale.IsAdicLisseSheaf.exists_map_fieldExtHom_eq`). It is the displayed
identification `(j_* F)_x̄ ≅ F_η̄^{I_x}` of blueprint `lemma-boundary-stalk--1`, given the
strictly henselian neighbourhood; the Frobenius equivariance and the comparison of `F(Spec Ω)`
with the Weil fundamental representation are not treated here.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **The boundary stalk of `j_* F` as Galois invariants.** Let `h : Spec A ⟶ C̄` be a weakly étale
neighbourhood of the geometric point `x̄` of a closed point `x` through the closed point of the
strictly henselian `Spec A`, whose punctured part `Spec A ×_C̄ Ū` is identified, as a pro-étale
`Ū`-scheme, with `k : Spec K' ⟶ Ū`, and let `Ω / K'` be a Galois extension. For a lisse Weil
sheaf `F` on `U₀` there is an injective `ℚ̄_ℓ`-linear map `(j_* F)_x̄ ⟶ F(Spec Ω)` whose image
is the module of `Gal(Ω / K')`-invariants.
(blueprint: `lemma-boundary-stalk--1`, the displayed identification) -/
theorem exists_injective_stalk_directImage_range_eq_invariants {U C : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [C.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (C ↘ Spec (CommRingCat.of k₀))]
    (j : U ⟶ C) [IsOpenImmersion j] [QuasiCompact j] [j.IsOver (Spec (CommRingCat.of k₀))]
    {F : WeilSheaf k₀ l U} (hF : F.IsLisse) (x : C.finitePoints) {A : Type u} [CommRing A]
    [IsStrictlyHenselianLocalRing A]
    (h : Spec (.of A) ⟶ (C ↘ Spec (CommRingCat.of k₀)).geometricFiber) [WeaklyEtale h]
    (t : Scheme.ProEt.mk (𝟙 _) ⟶ (MorphismProperty.Over.pullback @WeaklyEtale ⊤
      ((C ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x)).obj
        (Scheme.ProEt.mk h))
    (ht : (t.left ≫ pullback.fst h _) (IsLocalRing.closedPoint (AlgebraicClosure k₀)) =
      IsLocalRing.closedPoint A)
    {K' Ω : Type u} [Field K'] [Field Ω] [Algebra K' Ω] [Algebra.IsSeparable K' Ω] [Normal K' Ω]
    (k : Spec (.of K') ⟶ (U ↘ Spec (CommRingCat.of k₀)).geometricFiber) [WeaklyEtale k]
    (e : Scheme.ProEt.mk k ≅ (MorphismProperty.Over.pullback @WeaklyEtale ⊤
      (Scheme.Hom.geometricFiberMap j (comp_over j _))).obj (Scheme.ProEt.mk h)) :
    ∃ φ : (((directImage j).obj F).stalk x).carrier →ₗ[PadicAlgCl l]
        (WeilCoefficients.toModuleCat l).obj (F.obj.carrier.X.obj.obj (op (fieldExtObj Ω k))),
      Function.Injective φ ∧ ∀ v, v ∈ LinearMap.range φ ↔
        ∀ σ : Ω ≃ₐ[K'] Ω, F.obj.carrier.X.obj.map (fieldExtAut k σ).op v = v := by
  set P := (Scheme.Hom.geometricFiberMap j (comp_over j _))_*[WeilCoefficients.{u} l].obj
    F.obj.carrier.X
  set g := germ (WeilCoefficients.{u} l)
    ((C ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x) P t
  have hg : Function.Bijective g := bijective_germ_stalk_directImage j F x h t ht
  have : IsIso g := (ConcreteCategory.isIso_iff_bijective g).2 hg
  -- sections of `P` over `Spec A` are sections of `F` over `Spec K'`
  let r : P.obj.obj (op (Scheme.ProEt.mk h)) ⟶
      F.obj.carrier.X.obj.obj (op (fieldExtObj Ω k)) :=
    F.obj.carrier.X.obj.map e.hom.op ≫ F.obj.carrier.X.obj.map (fieldExtHom Ω k).op
  refine ⟨((WeilCoefficients.toModuleCat l).map (inv g ≫ r)).hom, ?_, fun v ↦ ⟨?_, fun hv ↦ ?_⟩⟩
  · have hr : Function.Injective r := by
      have he : Function.Injective (F.obj.carrier.X.obj.map e.hom.op) :=
        (ConcreteCategory.bijective_of_isIso (F.obj.carrier.X.obj.map e.hom.op)).1
      exact (hF.injective_map_fieldExtHom k).comp he
    have hi : Function.Injective (inv g) := (ConcreteCategory.bijective_of_isIso (inv g)).1
    exact hr.comp hi
  · rintro ⟨w, rfl⟩ σ
    change F.obj.carrier.X.obj.map (fieldExtAut k σ).op
        (F.obj.carrier.X.obj.map (fieldExtHom Ω k).op
          (F.obj.carrier.X.obj.map e.hom.op ((inv g) w))) =
      F.obj.carrier.X.obj.map (fieldExtHom Ω k).op
        (F.obj.carrier.X.obj.map e.hom.op ((inv g) w))
    exact map_fieldExtAut_map_fieldExtHom k σ _
  · obtain ⟨s, hs⟩ := hF.exists_map_fieldExtHom_eq k v hv
    refine ⟨g (F.obj.carrier.X.obj.map e.inv.op s), ?_⟩
    change r ((inv g) (g (F.obj.carrier.X.obj.map e.inv.op s))) = v
    rw [← ConcreteCategory.comp_apply g (inv g), IsIso.hom_inv_id, ConcreteCategory.id_apply]
    change F.obj.carrier.X.obj.map (fieldExtHom Ω k).op
      (F.obj.carrier.X.obj.map e.hom.op (F.obj.carrier.X.obj.map e.inv.op s)) = v
    have hee : F.obj.carrier.X.obj.map e.hom.op (F.obj.carrier.X.obj.map e.inv.op s) = s := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, e.hom_inv_id, op_id,
        CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
    rw [hee, hs]

end AlgebraicGeometry.WeilSheaf
