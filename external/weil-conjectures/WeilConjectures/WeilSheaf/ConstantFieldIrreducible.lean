/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.Extension
public import WeilConjectures.WeilSheaf.ConstantFieldPullback

/-!
# Irreducible lisse Weil sheaves over a smaller base field

Let `k₀ ⊆ k'` be finite fields with `[k' : k₀] = m + 1` and `V` a `k'`-scheme, regarded also as a
`k₀`-scheme. The equivalence `ProEtaleWeilSheaf k₀ l V ≌ ProEtaleWeilSheaf k' l V` taking the
first piece of the geometric fibre (`AlgebraicGeometry.ProEtaleWeilSheaf.constantFieldFunctor`)
preserves and reflects lissity, since the pieces of the geometric fibre form an open covering
and all pieces of a Weil sheaf are isomorphic to the first one. Hence it sends irreducible lisse
Weil sheaves relative to `k₀` to irreducible lisse Weil sheaves relative to `k'`
(`AlgebraicGeometry.WeilSheaf.IsIrreducibleLisse.constantFieldFunctor`), and a Weil sheaf which
becomes a constant twist of a pulled-back lisse sheaf relative to `k'` is one relative to `k₀`
(`AlgebraicGeometry.WeilSheaf.exists_iso_constantTwist_geometricFiberPullback_of_constantField`).
-/

@[expose] public section

universe u

open CategoryTheory Endofunctor Limits

noncomputable section

namespace AlgebraicGeometry

open ProEtale

namespace ProEtaleWeilSheaf

variable {k₀ k' : Type u} [Field k₀] [Field k'] [Finite k₀] [Finite k'] [Algebra k₀ k']
  (l : ℕ) [Fact l.Prime] {V : Scheme.{u}} [V.Over (Spec (CommRingCat.of k₀))]
  [V.Over (Spec (CommRingCat.of k'))]
  (hc : (V ↘ Spec (CommRingCat.of k')) ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k')) =
    V ↘ Spec (CommRingCat.of k₀))
  {m : ℕ} (hm : Module.finrank k₀ k' = m + 1)

/-- A pro-étale Weil sheaf relative to `k₀` is lisse if its first piece is: the pieces of the
geometric fibre form an open covering, and every piece of the sheaf is isomorphic to the first
one through the Weil structure. -/
theorem isAdicLisseSheaf_of_constantFieldFunctor {K : ProEtaleWeilSheaf k₀ l V}
    (hK : IsAdicLisseSheaf ((constantFieldFunctor l hc hm).obj K).carrier) :
    IsAdicLisseSheaf K.carrier := by
  refine IsAdicLisseSheaf.of_presieve (Presieve.ofArrows _ (pieceMap (m := m) hc))
    (Scheme.zariskiPrecoverage_le_proetalePrecoverage _
      ((Scheme.ofArrows_mem_precoverage_iff _).mpr
        ⟨fun x ↦ (existsUnique_mem_range_pieceMap hc hm x).exists,
          fun i ↦ inferInstanceAs (IsOpenImmersion (pieceMap hc i))⟩)) ?_
  rintro _ _ ⟨i⟩
  exact hK.of_iso ((cyclicDecomposition l hc hm).chain K i).symm

end ProEtaleWeilSheaf

namespace WeilSheaf

variable {k₀ k' : Type u} [Field k₀] [Field k'] [Finite k₀] [Finite k'] [Algebra k₀ k']
  {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k' ≠ l)]
  {V : Scheme.{u}} [V.Over (Spec (CommRingCat.of k₀))] [V.Over (Spec (CommRingCat.of k'))]
  (hc : (V ↘ Spec (CommRingCat.of k')) ≫ Spec.map (CommRingCat.ofHom (algebraMap k₀ k')) =
    V ↘ Spec (CommRingCat.of k₀))
  {m : ℕ} (hm : Module.finrank k₀ k' = m + 1)

/-- The first piece of the geometric fibre, on Weil sheaves: the pullback of a constructible
sheaf is constructible. -/
def constantFieldFunctor : WeilSheaf k₀ l V ⥤ WeilSheaf k' l V :=
  (WeilSheaf.objectProperty k₀ l V).liftFullSubcategory (WeilSheaf.objectProperty k' l V)
    (ProEtaleWeilSheaf.constantFieldFunctor l hc hm) fun _ hF ↦ hF.upperStar _

instance : (constantFieldFunctor (l := l) hc hm).Full :=
  ObjectProperty.liftFullSubcategory_full _ _ _ _

instance : (constantFieldFunctor (l := l) hc hm).Faithful :=
  ObjectProperty.liftFullSubcategory_faithful _ _ _ _

/-- The first piece of the geometric fibre is fully faithful on Weil sheaves. -/
def constantFieldFunctorFullyFaithful : (constantFieldFunctor (l := l) hc hm).FullyFaithful :=
  .ofFullyFaithful _

instance : (constantFieldFunctor (l := l) hc hm).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_full _

instance : (constantFieldFunctor (l := l) hc hm).ReflectsMonomorphisms :=
  Functor.reflectsMonomorphisms_of_faithful _

/-- **Irreducible lisse Weil sheaves over a smaller base field**: the first piece of an
irreducible lisse Weil sheaf relative to `k₀` is an irreducible lisse Weil sheaf relative to
`k'`. A lisse subsheaf of the first piece is the first piece of a Weil sheaf relative to `k₀`,
which is lisse (`ProEtaleWeilSheaf.isAdicLisseSheaf_of_constantFieldFunctor`). -/
theorem IsIrreducibleLisse.constantFieldFunctor {G : WeilSheaf k₀ l V}
    (hG : G.IsIrreducibleLisse) :
    ((WeilSheaf.constantFieldFunctor hc hm).obj G).IsIrreducibleLisse := by
  obtain ⟨hl, hz, hsub⟩ := hG
  refine ⟨hl.upperStar _, fun h ↦ hz ?_, fun G' i hi hG' ↦ ?_⟩
  · rw [IsZero.iff_id_eq_zero] at h ⊢
    exact (WeilSheaf.constantFieldFunctor hc hm).map_injective (by simpa using h)
  · let P := ProEtaleWeilSheaf.constantFieldFunctor l hc hm
    let K := P.objPreimage G'.obj
    let e : P.obj K ≅ G'.obj := P.objObjPreimageIso G'.obj
    have hK : IsAdicLisseSheaf K.carrier :=
      ProEtaleWeilSheaf.isAdicLisseSheaf_of_constantFieldFunctor l hc hm
        (IsAdicLisseSheaf.of_iso ((IsoAlgebra.forget _).mapIso e).symm hG')
    let K' : WeilSheaf k₀ l V := ⟨K, hK.isAdicConstructibleSheaf⟩
    let e' : (WeilSheaf.constantFieldFunctor hc hm).obj K' ≅ G' := ObjectProperty.isoMk _ e
    let j : K' ⟶ G := (WeilSheaf.constantFieldFunctor hc hm).preimage (e'.hom ≫ i)
    have hj : Mono j := (WeilSheaf.constantFieldFunctor hc hm).mono_of_mono_map (by
      rw [Functor.map_preimage]
      infer_instance)
    rcases hsub K' j hj hK with h | h
    · exact Or.inl (((WeilSheaf.constantFieldFunctor hc hm).map_isZero h).of_iso e'.symm)
    · refine Or.inr ?_
      have : IsIso ((WeilSheaf.constantFieldFunctor hc hm).map j) := inferInstance
      rw [Functor.map_preimage] at this
      exact IsIso.of_isIso_comp_left e'.hom i

/-- The pullback `p₀^* H ⊗ 𝓑_b` relative to `k₀` goes to `p'^* H ⊗ 𝓑_{b^{m+1}}` relative to
`k'` (`ProEtaleWeilSheaf.constantFieldFunctorObjGeometricFiberPullbackTwistIso`). -/
def constantFieldFunctorObjConstantTwistIso {H : AdicSheaf l V} (hH : IsAdicLisseSheaf H)
    (b : (PadicAlgCl l)ˣ) :
    (constantFieldFunctor hc hm).obj ((geometricFiberPullback (k₀ := k₀) hH).constantTwist b) ≅
      (geometricFiberPullback (k₀ := k') hH).constantTwist (b ^ (m + 1)) :=
  ObjectProperty.isoMk _
    (ProEtaleWeilSheaf.constantFieldFunctorObjGeometricFiberPullbackTwistIso l hc hm H b)

/-- **Descent up to twist over a smaller base field**: if the first piece of a Weil sheaf `G`
relative to `k₀` is a constant twist of the pullback of a lisse sheaf `H` on `V` relative to `k'`,
then so is `G` relative to `k₀`, the twist being by an `(m+1)`-st root. -/
theorem exists_iso_constantTwist_geometricFiberPullback_of_constantField {G : WeilSheaf k₀ l V}
    {H : AdicSheaf l V} (hH : IsAdicLisseSheaf H) (b' : (PadicAlgCl l)ˣ)
    (e : (constantFieldFunctor hc hm).obj G ≅
      (geometricFiberPullback (k₀ := k') hH).constantTwist b') :
    ∃ b : (PadicAlgCl l)ˣ,
      Nonempty (G ≅ (geometricFiberPullback (k₀ := k₀) hH).constantTwist b) := by
  obtain ⟨c, hc'⟩ := IsAlgClosed.exists_pow_nat_eq (b' : PadicAlgCl l) (Nat.succ_pos m)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.succ_ne_zero m)] at hc'
    exact b'.ne_zero hc'.symm
  let b := Units.mk0 c hc0
  have hb : b ^ (m + 1) = b' := Units.ext (by simpa [b] using hc')
  refine ⟨b, ⟨(constantFieldFunctorFullyFaithful hc hm).preimageIso (e ≪≫ ?_)⟩⟩
  exact (hb ▸ constantFieldFunctorObjConstantTwistIso hc hm hH b).symm

end WeilSheaf

end AlgebraicGeometry
