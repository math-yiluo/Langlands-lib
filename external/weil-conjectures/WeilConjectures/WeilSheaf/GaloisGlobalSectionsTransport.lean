/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.CondensedModelGaloisTrace
public import WeilConjectures.TraceFormula.FrobeniusFixedPointsEquiv
public import WeilConjectures.TraceFormula.FrobeniusFixedPointsFinite
public import WeilConjectures.WeilSheaf.GeometricFiberPullback
public import WeilConjectures.WeilSheaf.StalkComparison
public import WeilConjectures.WeilSheaf.StalkUpperStar

/-!
# Galois actions on global sections as transports

Auxiliary results for the trace function of a Weil sheaf pulled back from the model
(`WeilConjectures.WeilSheaf.GeometricFiberPullbackTrace`): the canonical morphism
`g^* p^* N ⟶ p^* N` for `g ≫ p = p` (`AlgebraicGeometry.ProEtale.upperStarInvariantHom`), the
transports of global sections along it
(`AlgebraicGeometry.ProEtale.globalSectionsTransport_upperStarId_hom_app`), the Galois action on
global sections in these terms (`AlgebraicGeometry.ProEtale.galoisGlobalSections_eq`), and the
invariance of traces under conjugation
(`AlgebraicGeometry.WeilCoefficients.trace_toModuleCat_map_eq_of_comp_eq`).
-/


@[expose] public section

universe u u'

open CategoryTheory

open scoped AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The canonical morphism `g^* p^* N ≅ (g ≫ p)^* N = p^* N` for an endomorphism `g` with
`g ≫ p = p`. -/
noncomputable def upperStarInvariantHom {Z Y : Scheme.{u}} (p : Z ⟶ Y) {g : Z ⟶ Z}
    (hg : g ≫ p = p) (N : Sheaf (Scheme.ProEt.topology Y) A) :
    (g)^*[A].obj ((p)^*[A].obj N) ⟶ (p)^*[A].obj N :=
  (upperStarComp A g p).inv.app N ≫ (upperStarCongr A hg).hom.app N

/-- The canonical morphisms `g^* p^* N ⟶ p^* N` along equal endomorphisms agree. -/
lemma upperStarCongr_hom_app_comp_upperStarInvariantHom {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    {g g' : Z ⟶ Z} (e : g = g') (hg : g ≫ p = p) (hg' : g' ≫ p = p)
    (N : Sheaf (Scheme.ProEt.topology Y) A) :
    (upperStarCongr A e).hom.app ((p)^*[A].obj N) ≫ upperStarInvariantHom A p hg' N =
      upperStarInvariantHom A p hg N := by
  subst e
  simp [upperStarCongr]

/-- Three congruence isomorphisms of pullbacks compose to one; the composite equality is an
independent hypothesis, so that the kernel never compares proofs of equalities of morphisms. -/
lemma upperStarCongr_hom_app_trans_trans {P Q : Scheme.{u}} {x y z w : P ⟶ Q} (h : x = y)
    (h' : y = z) (h'' : z = w) (e : x = w) (N : Sheaf (Scheme.ProEt.topology Q) A) :
    (upperStarCongr A h).hom.app N ≫ (upperStarCongr A h').hom.app N ≫
        (upperStarCongr A h'').hom.app N =
      (upperStarCongr A e).hom.app N := by
  subst h h' h''
  simp [upperStarCongr]

/-- **The cocycle condition** of the canonical morphisms `g^* p^* N ⟶ p^* N`: for `b ≫ c = a`,
the canonical morphism along `a` is `a^* p^* N ≅ b^* c^* p^* N ⟶ b^* p^* N ⟶ p^* N`. -/
lemma upperStarFactor_hom_app_comp_upperStarInvariantHom {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    {a b c : Z ⟶ Z} (e : b ≫ c = a) (ha : a ≫ p = p) (hb : b ≫ p = p) (hc : c ≫ p = p)
    (N : Sheaf (Scheme.ProEt.topology Y) A) :
    (upperStarFactor A e).hom.app ((p)^*[A].obj N) ≫
        (b)^*[A].map (upperStarInvariantHom A p hc N) ≫ upperStarInvariantHom A p hb N =
      upperStarInvariantHom A p ha N := by
  subst e
  rw [upperStarFactor_rfl, ← cancel_epi ((upperStarComp A (b ≫ c) p).hom.app N),
    reassoc_of% upperStarComp_hom_app_comp_upperStarComp_hom_app, upperStarInvariantHom,
    upperStarInvariantHom, upperStarInvariantHom, Functor.map_comp_assoc,
    ← Functor.map_comp_assoc (b)^*[A] ((upperStarComp A c p).hom.app N), Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc,
    ← reassoc_of% upperStarCongr_hom_app_comp_upperStarComp_hom_app' A b hc N,
    Iso.hom_inv_id_app_assoc]
  exact upperStarCongr_hom_app_trans_trans A _ _ _ _ N

/-- Two congruence isomorphisms of pullbacks compose to one; the composite equality is an
independent hypothesis. -/
@[reassoc]
lemma upperStarCongr_hom_app_trans_eq {P Q : Scheme.{u}} {x y z : P ⟶ Q} (h : x = y)
    (h' : y = z) (e : x = z) (N : Sheaf (Scheme.ProEt.topology Q) A) :
    (upperStarCongr A h).hom.app N ≫ (upperStarCongr A h').hom.app N =
      (upperStarCongr A e).hom.app N := by
  subst h h'
  simp [upperStarCongr]

/-- The composition isomorphism with the identity, followed by `𝟙^* ≅ 𝟭`, is the transport along
`t ≫ 𝟙 = t`. -/
@[reassoc]
lemma upperStarComp_id_right_hom_app_comp_map_upperStarId_hom_app {S Y : Scheme.{u}}
    (t : S ⟶ Y) (N : Sheaf (Scheme.ProEt.topology Y) A) :
    (upperStarComp A t (𝟙 Y)).hom.app N ≫ (t)^*[A].map ((upperStarId A Y).hom.app N) =
      (upperStarCongr A (Category.comp_id t)).hom.app N := by
  rw [upperStarComp_id_right, Iso.trans_hom, Iso.trans_hom, NatTrans.comp_app,
    NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom,
    Iso.symm_hom, Functor.leftUnitor_inv_app, Category.id_comp, Category.assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

/-- The transport of global sections along a square `τ ≫ x = x ≫ 𝟙` and `𝟙^* ≅ 𝟭` is the Galois
action `Γ(x^* N) ⟶ Γ(τ^* x^* N) ≅ Γ((τ ≫ x)^* N) = Γ(x^* N)`. -/
lemma globalSectionsTransport_upperStarId_hom_app {S Y : Scheme.{u}} {τ : S ⟶ S} {x : S ⟶ Y}
    (hY : τ ≫ x = x ≫ 𝟙 Y) (h : τ ≫ x = x) (N : Sheaf (Scheme.ProEt.topology Y) A) :
    globalSectionsTransport A hY ((upperStarId A Y).hom.app N) =
      (globalSectionsToUpperStar A τ).app ((x)^*[A].obj N) ≫
        (Sheaf.Γ _ A).map ((upperStarComp A τ x).inv.app N ≫ (upperStarCongr A h).hom.app N) := by
  rw [globalSectionsTransport, upperStarCompIso_hom_app, Category.assoc, Category.assoc,
    upperStarComp_id_right_hom_app_comp_map_upperStarId_hom_app,
    upperStarCongr_hom_app_trans_eq A hY (Category.comp_id x) h]

/-- `AlgebraicGeometry.ProEtale.adicUpperStarCongr_hom_app_hom`, elaborated with the shortcut
instance `ModuleCat.isGrothendieckAbelian_of_commRing` (that lemma uses Mathlib's instance). The
kernel compares the two forms of `(upperStarCongr _ h).hom.app` only by unfolding everything. -/
lemma adicUpperStarCongr_hom_app_hom' {l : ℕ} [Fact l.Prime] {Z Y : Scheme.{u}} {g g' : Z ⟶ Y}
    (h : g = g') (M : AdicSheaf l Y) :
    ((adicUpperStarCongr l h).hom.app M).hom =
      (upperStarCongr (WeilCoefficients.{u} l) h).hom.app M.X := by
  subst h
  rfl

/-- The Galois action on global sections, written with the pullback of the underlying sheaf. -/
lemma galoisGlobalSections_eq {l : ℕ} [Fact l.Prime] {S X : Scheme.{u}} (σ : S ⟶ S) (x : S ⟶ X)
    (h : σ ≫ x = x) (H : AdicSheaf l X) :
    galoisGlobalSections σ x h H =
      (globalSectionsToUpperStar (WeilCoefficients.{u} l) σ).app
          ((x)^*[WeilCoefficients.{u} l].obj H.X) ≫
        (Sheaf.Γ _ (WeilCoefficients.{u} l)).map
          ((upperStarComp (WeilCoefficients.{u} l) σ x).inv.app H.X ≫
            (upperStarCongr (WeilCoefficients.{u} l) h).hom.app H.X) := by
  rw [galoisGlobalSections, Mod.comp_hom', adicUpperStarComp_inv_app_hom,
    adicUpperStarCongr_hom_app_hom']
  rfl

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry

open ProEtale

/-- Endomorphisms of `ℚ̄_ℓ`-modules intertwined by an isomorphism have the same trace. -/
lemma WeilCoefficients.trace_toModuleCat_map_eq_of_comp_eq {l : ℕ} [Fact l.Prime]
    {V W : WeilCoefficients.{u} l} (E : V ≅ W) {T : V ⟶ V} {T' : W ⟶ W}
    (h : T ≫ E.hom = E.hom ≫ T') :
    LinearMap.trace (PadicAlgCl l) _ ((WeilCoefficients.toModuleCat l).map T).hom =
      LinearMap.trace (PadicAlgCl l) _ ((WeilCoefficients.toModuleCat l).map T').hom := by
  have hT' : T' = E.inv ≫ T ≫ E.hom := by rw [h, Iso.inv_hom_id_assoc]
  rw [hT', ← LinearMap.trace_conj' ((WeilCoefficients.toModuleCat l).map T).hom
    (WeilCoefficients.linearEquivOfIso E)]
  congr 1

/-- The `m`-th powers of the two forms `specGeometricFrobenius` and `geometricFrobeniusField` of the
geometric Frobenius `σ` of `Spec k̄` agree. -/
lemma specGeometricFrobenius_pow_hom_eq_geometricFrobeniusField_pow_hom (k : Type u) [Field k]
    [Finite k] (m : ℕ) :
    (specGeometricFrobenius k ^ m).asIso.hom = ((geometricFrobeniusField k).pow m).hom := by
  let := Fintype.ofFinite k
  have e : FiniteField.geometricFrobeniusAlgEquivOfAlgebraic k (AlgebraicClosure k) =
      FiniteField.geometricFrobenius k (AlgebraicClosure k) := by
    ext x
    refine ((FiniteField.geometricFrobenius_eq_iff k (AlgebraicClosure k)).2 ?_).symm
    rw [Nat.card_eq_fintype_card, FiniteField.geometricFrobeniusAlgEquivOfAlgebraic_eq_inv,
      ← FiniteField.frobeniusAlgEquivOfAlgebraic_apply, ← AlgEquiv.mul_apply, mul_inv_cancel,
      AlgEquiv.one_apply]
  rw [specGeometricFrobenius_pow_hom, Iso.pow_hom_eq_pow,
    ProEtale.CondensedRing.geometricFrobeniusField_hom_pow, e]

end AlgebraicGeometry
