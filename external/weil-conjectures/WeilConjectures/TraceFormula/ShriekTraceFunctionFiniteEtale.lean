/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.FiniteEtaleStalkTrace
public import WeilConjectures.TraceFormula.HomologyWeilLowerShriek
public import WeilConjectures.TraceFormula.ShriekTraceFunction
public import WeilConjectures.TraceFormula.StalkDualizable

/-!

# The sheaf–function compatibility along a finite étale morphism

For a finite étale morphism `f : X ⟶ Y` with automorphisms `e_X`, `e_Y` such that
`e_X ≫ f = f ≫ e_Y`, the sheaf–function compatibility `ShriekTraceFunctionAt` holds
(`ProEtale.CondensedRing.ShriekTraceFunctionAt.of_isFinite_of_etale`): this is the
Grothendieck–Lefschetz formula in dimension zero. The proof:

1. `Hʲ(Rf_!^Weil K) ≅ f_* Hʲ(K)` as Weil sheaves
   (`ProEtale.CondensedRing.nonempty_homologyFunctor_weilLowerShriek_iso`);
2. the iterated Weil structure of `f_* Hʲ(K)` is the pushforward of the iterated structure of
   `Hʲ(K)` (`ProEtale.CondensedRing.nonempty_pow_weilSheafLowerStar_iso`);
3. the stalk of `f_* Hʲ(K)` at `ȳ` is the product of the stalks of `Hʲ(K)` at the points over `ȳ`,
   permuted by the Frobenius, so its trace is the sum of the traces at the fixed points
   (`ProEtale.CondensedRing.weilSheafStalkTrace_weilSheafLowerStar`), the stalks being
   dualizable (`ProEtale.CondensedRing.nonempty_hasRightDual_upperStar_homology`);
4. the sums over `j` and over the points are exchanged.

-/

@[expose] public section

universe u

open CategoryTheory Endofunctor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Finite k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X Y : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (eX : X ≅ X) (eY : Y ≅ Y) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)
section FrobeniusStalk

variable {Z : Over (Spec (.of k))} {e : Z ≅ Z} (n : ℕ)
  (x : Spec (.of (AlgebraicClosure k)) ⟶ Z.left)
  (hx : x ≫ (e.pow (n + 1)).hom.left = ((geometricFrobeniusField k).pow (n + 1)).hom ≫ x)
  (F : WeilSheaf ℓ e)

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
lemma WeilSheaf.powStalkFunctor_eq_comp : WeilSheaf.powStalkFunctor ℓ (n + 1) x hx =
    WeilSheaf.powFunctor ℓ e (n + 1) ⋙
      WeilSheaf.stalkFunctor ℓ (e.pow (n + 1)) ((geometricFrobeniusField k).pow (n + 1)).hom x hx :=
  WeilSheaf.powStalkFunctor.eq_1 ℓ (n + 1) x hx

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
lemma WeilSheaf.powStalkFunctor_obj : (WeilSheaf.powStalkFunctor ℓ (n + 1) x hx).obj F =
    (WeilSheaf.powFunctor ℓ e (n + 1) ⋙ WeilSheaf.stalkFunctor ℓ (e.pow (n + 1))
      ((geometricFrobeniusField k).pow (n + 1)).hom x hx).obj F :=
  congrArg (fun G ↦ G.obj F) (WeilSheaf.powStalkFunctor_eq_comp ℓ n x hx)

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
lemma WeilSheaf.powFunctor_comp_stalkFunctor_obj : (WeilSheaf.powFunctor ℓ e (n + 1) ⋙
    WeilSheaf.stalkFunctor ℓ (e.pow (n + 1)) ((geometricFrobeniusField k).pow (n + 1)).hom x
        hx).obj F =
      (WeilSheaf.stalkFunctor ℓ (e.pow (n + 1)) ((geometricFrobeniusField k).pow (n + 1)).hom x
        hx).obj ((WeilSheaf.powFunctor ℓ e (n + 1)).obj F) :=
  Functor.comp_obj _ _ F

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- The stalk with its `(n + 1)`-st Frobenius operator is the stalk of the Weil sheaf `F^{(n+1)}`
for `e^{n+1}`. The proof goes through separately stated steps, which keeps the kernel from
unfolding the stalk functor. -/
lemma WeilSheaf.frobeniusStalk_eq : WeilSheaf.frobeniusStalk ℓ (n + 1) x hx F =
    (WeilSheaf.stalkFunctor ℓ (e.pow (n + 1)) ((geometricFrobeniusField k).pow (n + 1)).hom x
      hx).obj (WeilSheaf.pow ℓ F (n + 1)) :=
  ((WeilSheaf.powStalkFunctor_obj ℓ n x hx F).trans
    (WeilSheaf.powFunctor_comp_stalkFunctor_obj ℓ n x hx F)).trans
    (congrArg _ (WeilSheaf.powFunctor_obj ℓ (n + 1) F))

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] in
/-- **The local trace through the explicit stalk Frobenius**: the trace `Tr(Fr_{x̄,n+1} | F_x̄)`
of a Weil sheaf `F` for `e` at a point of degree `n + 1` is the trace of the explicit Frobenius
`stalkFrobenius` of the stalk of the Weil sheaf `F^{(n+1)}` for `e^{n+1}`. -/
theorem weilSheafStalkTrace_eq_stalkFrobeniusTrace :
    weilSheafStalkTrace ℓ (n + 1) x hx F = stalkFrobeniusTrace ℓ
      (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ)
        ((geometricFrobeniusField k).pow (n + 1)).hom)
      (e.pow (n + 1)) hx (WeilSheaf.pow ℓ F (n + 1)).str.hom := by
  rw [weilSheafStalkTrace, WeilSheaf.frobeniusStalk_eq, WeilSheaf.stalkFunctor_obj_str_hom]
  rfl

end FrobeniusStalk

omit [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)] [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
  [IsSeparated Y.hom] in
/-- The trace of the Frobenius on the stalk of the pushforward `f_* F` of a Weil sheaf along a
finite étale morphism at a point `ȳ` of degree `n + 1` is the sum of the traces at the points of
degree `n + 1` over `ȳ`, provided the stalks of `F` over `ȳ` are dualizable. -/
theorem weilSheafStalkTrace_weilSheafLowerStar [IsFinite f.left] [Etale f.left] (n : ℕ)
    (y : frobeniusFixedPoints eY (n + 1)) (F : WeilSheaf ℓ eX)
    (hF : ∀ {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X.left),
      Nonempty (HasRightDual ((x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj F.carrier))) :
    weilSheafStalkTrace ℓ (n + 1) y.1 y.2.2 ((weilSheafLowerStar ℓ eX eY hf).obj F) =
      ∑ᶠ x : {x : frobeniusFixedPoints eX (n + 1) // x.1 ≫ f.left = y.1},
        weilSheafStalkTrace ℓ (n + 1) x.1.1 x.1.2.2 F := by
  obtain ⟨i⟩ := nonempty_pow_weilSheafLowerStar_iso ℓ eX eY hf F n
  exact (weilSheafStalkTrace_eq_stalkFrobeniusTrace ℓ n y.1 y.2.2 _).trans <|
    (stalkFrobeniusTrace_congr ℓ _ _ y.2.2 i).trans <|
    (stalkFrobeniusTrace_weilSheafLowerStar ℓ (eX.pow (n + 1)) (eY.pow (n + 1)) _ _
      (Ω := AlgebraicClosure k) (Iso.refl _) y.2.2 _
      (fun x ↦ by
        rw [← WeilSheaf.powFunctor_obj, WeilSheaf.powFunctor_obj, WeilSheaf.pow_carrier]
        exact hF x.1)
      (fun x : {x : frobeniusFixedPoints eX (n + 1) // x.1 ≫ f.left = y.1} ↦ x.1.1)
      (fun x ↦ x.2) (fun x ↦ x.1.2.2)
      (fun a b h ↦ Subtype.ext (Subtype.ext h))
      (fun x hx hx' ↦ ⟨⟨⟨x, by rw [← Over.w f, ← Category.assoc, hx, y.2.1], hx'⟩, hx⟩,
        rfl⟩)).trans <|
    finsum_congr fun x ↦ (weilSheafStalkTrace_eq_stalkFrobeniusTrace ℓ n x.1.1 x.1.2.2 F).symm

/-- The stalk traces of the homology sheaves of `Rf_! K` at `ȳ` are the sums of those of `K` at
the points of degree `n + 1` over `ȳ`. -/
theorem weilSheafStalkTrace_homology_weilLowerShriek [IsFinite f.left] [Etale f.left]
    (K : WeilBoundedConstructible ℓ eX.hom) (n : ℕ) (y : frobeniusFixedPoints eY (n + 1)) (j : ℤ) :
    weilSheafStalkTrace ℓ (n + 1) y.1 y.2.2
      ((WeilBoundedConstructible.homologyFunctor ℓ eY j).obj ((weilLowerShriek ℓ eX eY hf).obj K)) =
      ∑ᶠ x : {x : frobeniusFixedPoints eX (n + 1) // x.1 ≫ f.left = y.1},
        weilSheafStalkTrace ℓ (n + 1) x.1.1 x.1.2.2
          ((WeilBoundedConstructible.homologyFunctor ℓ eX j).obj K) := by
  obtain ⟨i⟩ := nonempty_homologyFunctor_weilLowerShriek_iso ℓ eX eY hf K j
  rw [weilSheafStalkTrace_congr ℓ (n + 1) y.1 y.2.2 i]
  exact weilSheafStalkTrace_weilSheafLowerStar ℓ eX eY hf n y _
    fun x ↦ nonempty_hasRightDual_upperStar_homology ℓ K.carrier j x

/-- **Dimension zero**: the sheaf–function compatibility holds along a finite étale morphism. -/
theorem ShriekTraceFunctionAt.of_isFinite_of_etale [IsFinite f.left] [Etale f.left] :
    ShriekTraceFunctionAt ℓ eX eY hf := by
  intro K n y
  classical
  have := finite_fibrePoints f.left y.1 (Ω := AlgebraicClosure k) (Iso.refl _)
  have : Finite {x : frobeniusFixedPoints eX (n + 1) // x.1 ≫ f.left = y.1} :=
    Finite.of_injective (fun x ↦ (⟨x.1.1, x.2⟩ : FibrePoints f.left y.1))
      fun a b h ↦ Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val h))
  let := Fintype.ofFinite {x : frobeniusFixedPoints eX (n + 1) // x.1 ≫ f.left = y.1}
  have hsupp : ∀ x ∈ (Finset.univ :
      Finset {x : frobeniusFixedPoints eX (n + 1) // x.1 ≫ f.left = y.1}),
      (Function.support fun j : ℤ ↦ (j.negOnePow : ℤ) • weilSheafStalkTrace ℓ (n + 1) x.1.1 x.1.2.2
        ((WeilBoundedConstructible.homologyFunctor ℓ eX j).obj K)).Finite := fun x _ ↦
    (finite_support_weilSheafStalkTrace_homology ℓ (n + 1) x.1.1 x.1.2.2 K).subset
      (Function.support_smul_subset_right _ _)
  calc weilStalkTraceAlternatingSum ℓ (n + 1) y.1 y.2.2 ((weilLowerShriek ℓ eX eY hf).obj K)
      = ∑ᶠ j : ℤ, ∑ x : {x : frobeniusFixedPoints eX (n + 1) // x.1 ≫ f.left = y.1},
          (j.negOnePow : ℤ) • weilSheafStalkTrace ℓ (n + 1) x.1.1 x.1.2.2
            ((WeilBoundedConstructible.homologyFunctor ℓ eX j).obj K) := by
        rw [weilStalkTraceAlternatingSum]
        refine finsum_congr fun j ↦ ?_
        rw [weilSheafStalkTrace_homology_weilLowerShriek, finsum_eq_sum_of_fintype,
          Finset.smul_sum]
    _ = ∑ x : {x : frobeniusFixedPoints eX (n + 1) // x.1 ≫ f.left = y.1},
          weilStalkTraceAlternatingSum ℓ (n + 1) x.1.1 x.1.2.2 K := by
        rw [finsum_sum_comm _ _ hsupp]
        exact Finset.sum_congr rfl fun x _ ↦ rfl
    _ = _ := (finsum_eq_sum_of_fintype _).symm

end AlgebraicGeometry.ProEtale.CondensedRing
