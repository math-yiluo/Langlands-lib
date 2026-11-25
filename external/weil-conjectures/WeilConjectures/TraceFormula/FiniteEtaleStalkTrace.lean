/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.FiniteEtaleStalk
public import WeilConjectures.TraceFormula.CategoricalTraceBiproduct
public import WeilConjectures.TraceFormula.WeilSheafLowerStar
public import WeilConjectures.TraceFormula.WeilTrace

/-!

# The Frobenius trace on a stalk of the pushforward along a finite étale morphism

Let `f : X ⟶ Y` be a finite étale morphism and `ȳ : P ⟶ Y` a geometric point, `P ≅ Spec Ω` with
`Ω` separably closed, and let `σ` be an endomorphism of `P` with an isomorphism
`τ : σ^* ≅ 𝟭` of the pullback of module objects along `σ` with the identity. For a module object
`F` on `X`, the stalk of `f_* F` at `ȳ` is the product of the stalks of `F` at the points `x̄` of
`X` over `ȳ` (`ProEtale.CondensedRing.isLimit_stalkLowerStarFan`).

For automorphisms `e_X`, `e_Y` with `e_X ≫ f = f ≫ e_Y` and a Weil sheaf `F` for `e_X`, the
Frobenius of the stalk of the Weil sheaf `f_* F` at a point `ȳ` with `ȳ ≫ e_Y = σ ≫ ȳ` permutes
the factors: it sends the factor of `x̄⁺` to the factor of `x̄`, where `σ ≫ x̄⁺ = x̄ ≫ e_X`
(`ProEtale.CondensedRing.stalkFrobenius_lowerStar_comp_stalkLowerStarProj`). The factors fixed by
this permutation are those of the points with `x̄ ≫ e_X = σ ≫ x̄`, on which the Frobenius is the
Frobenius of the stalk of `F`. Hence the trace of the Frobenius of the stalk of `f_* F` at `ȳ` is
the sum of the traces of the Frobenius of the stalks of `F` at these points
(`ProEtale.CondensedRing.stalkFrobeniusTrace_lowerStar`), provided the stalks
are dualizable.

The statements are made for a scheme `P` and an isomorphism `τ`, rather than for `Spec Ω` and
`upperStarIsoIdOfIsSepClosed σ`: for `Ω = AlgebraicClosure k`, the ring structure of `Ω` found
through its field structure (as in `upperStarIsoIdOfIsSepClosed`) and the one found by instance
search agree only up to unfolding, and the kernel does not compare them efficiently under binders.

-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] {X Y : Over (Spec (.of k))}
  (eX : X ≅ X) (eY : Y ≅ Y) {f : X ⟶ Y} (hf : eX.hom ≫ f = f ≫ eY.hom)
  {P : Scheme.{u}} {σ : P ⟶ P} (τ : (σ)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ≅ 𝟭 _)

section StalkFrobenius

variable {Z : Over (Spec (.of k))} (e : Z ≅ Z)

/-- The Frobenius comparison `x̄'^* ≅ e^* ⋙ x̄^*` between points `x̄, x̄' : P ⟶ Z` with
`x̄ ≫ e = σ ≫ x̄'`: the composite
```
x̄'^* ≅ x̄'^* ⋙ σ^* ≅ (σ ≫ x̄')^* = (x̄ ≫ e)^* ≅ e^* ⋙ x̄^*
```
of `τ⁻¹` and the composition isomorphisms. For `P = Spec Ω`, `x̄' = x̄` and
`τ = upperStarIsoIdOfIsSepClosed σ` it is `weilStalkComparison` (`weilStalkComparison_eq`). -/
noncomputable def weilPointComparison {x x' : P ⟶ Z.left} (h : x ≫ e.hom.left = σ ≫ x') :
    (x')^*⟦Profinite.padicAlgClRingObj ℓ⟧ ⋙ 𝟭 _ ≅
      (e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧ ⋙ (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧ :=
  Functor.isoWhiskerLeft _ τ.symm ≪≫
    (upperStarComp (Profinite.padicAlgClRingObj ℓ) σ x').symm ≪≫
    eqToIso (congrArg (upperStar (Profinite.padicAlgClRingObj ℓ)) h.symm) ≪≫
    upperStarComp (Profinite.padicAlgClRingObj ℓ) x e.hom.left

/-- `weilStalkComparison` is `weilPointComparison` for `τ = upperStarIsoIdOfIsSepClosed σ`. -/
lemma weilStalkComparison_eq {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (σ : Spec (.of Ω) ⟶ Spec (.of Ω)) {x : Spec (.of Ω) ⟶ Z.left} (hx : x ≫ e.hom.left = σ ≫ x) :
    weilStalkComparison ℓ e σ x hx =
      weilPointComparison ℓ (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ) e
        hx := by
  unfold weilStalkComparison weilPointComparison
  rw [upperStarEqToIso_eq_eqToIso]

/-- The Frobenius of the stalk at a point `x̄ : P ⟶ Z` with `x̄ ≫ e = σ ≫ x̄` of a module object
`M` with a morphism `φ : e^* M ⟶ M`: the composite
```
x̄^* M ≅ σ^* x̄^* M ≅ (σ ≫ x̄)^* M = (x̄ ≫ e)^* M ≅ x̄^* e^* M ⟶ x̄^* M
```
of `weilPointComparison` and `x̄^* φ`. For a Weil sheaf `(M, φ)` it is the structure morphism of
its stalk (`WeilSheaf.stalkFunctor_obj_str_hom`). -/
noncomputable def stalkFrobenius {x : P ⟶ Z.left} (hx : x ≫ e.hom.left = σ ≫ x)
    {M : Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left)}
    (φ : (e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M ⟶ M) :
    (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M ⟶ (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M :=
  (weilPointComparison ℓ τ e hx).hom.app M ≫ (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map φ

/-- The trace of the stalk Frobenius `stalkFrobenius`. It is a separate definition taking the
point `x̄` as an argument, so that the kernel compares two such traces through their arguments
rather than by unfolding the pullbacks along the points. -/
noncomputable def stalkFrobeniusTrace {x : P ⟶ Z.left} (hx : x ≫ e.hom.left = σ ≫ x)
    {M : Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left)}
    (φ : (e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M ⟶ M) :
    End (MonoidalCategory.tensorUnit (Mod (Sheaf (Scheme.ProEt.topology P) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) P))) :=
  traceOrZero (stalkFrobenius ℓ τ e hx φ)

lemma stalkFrobeniusTrace_eq {x : P ⟶ Z.left} (hx : x ≫ e.hom.left = σ ≫ x)
    {M : Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left)}
    (φ : (e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M ⟶ M) :
    stalkFrobeniusTrace ℓ τ e hx φ = traceOrZero (stalkFrobenius ℓ τ e hx φ) :=
  rfl

/-- The stalk at a point `x̄ : P ⟶ Z` with `x̄ ≫ e = σ ≫ x̄` of Weil sheaves, with its Frobenius
`stalkFrobenius`. -/
noncomputable def WeilSheaf.pointStalkFunctor {x : P ⟶ Z.left} (hx : x ≫ e.hom.left = σ ≫ x) :
    WeilSheaf ℓ e ⥤ IsoAlgebra (𝟭 (Mod (Sheaf (Scheme.ProEt.topology P) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) P))) :=
  IsoAlgebra.mapOfNatIso (weilPointComparison ℓ τ e hx)

lemma WeilSheaf.pointStalkFunctor_obj_str {x : P ⟶ Z.left} (hx : x ≫ e.hom.left = σ ≫ x)
    (F : WeilSheaf ℓ e) :
    ((WeilSheaf.pointStalkFunctor ℓ τ e hx).obj F).str =
      (weilPointComparison ℓ τ e hx).app F.carrier ≪≫
        (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.mapIso F.str :=
  IsoAlgebra.mapOfNatIso_obj_str _ F

lemma WeilSheaf.pointStalkFunctor_obj_str_hom {x : P ⟶ Z.left} (hx : x ≫ e.hom.left = σ ≫ x)
    (F : WeilSheaf ℓ e) :
    ((WeilSheaf.pointStalkFunctor ℓ τ e hx).obj F).str.hom = stalkFrobenius ℓ τ e hx F.str.hom := by
  rw [WeilSheaf.pointStalkFunctor_obj_str, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rfl


/-- The trace of the stalk Frobenius only depends on the Weil sheaf up to isomorphism. -/
lemma stalkFrobeniusTrace_congr {x : P ⟶ Z.left} (hx : x ≫ e.hom.left = σ ≫ x)
    {F G : WeilSheaf ℓ e} (i : F ≅ G) :
    stalkFrobeniusTrace ℓ τ e hx F.str.hom = stalkFrobeniusTrace ℓ τ e hx G.str.hom := by
  have h := IsoAlgebra.traceOrZero_str_congr ((WeilSheaf.pointStalkFunctor ℓ τ e hx).mapIso i)
  rw [WeilSheaf.pointStalkFunctor_obj_str_hom, WeilSheaf.pointStalkFunctor_obj_str_hom] at h
  exact h.symm

/-- The trace of the stalk Frobenius only depends on the point up to equality. -/
lemma stalkFrobeniusTrace_congr_point {x x' : P ⟶ Z.left} (h : x = x')
    (hx : x ≫ e.hom.left = σ ≫ x) (hx' : x' ≫ e.hom.left = σ ≫ x')
    {M : Mod (Sheaf (Scheme.ProEt.topology Z.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) Z.left)}
    (φ : (e.hom.left)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj M ⟶ M) :
    stalkFrobeniusTrace ℓ τ e hx φ = stalkFrobeniusTrace ℓ τ e hx' φ := by
  subst h
  rfl

/-- The structure morphism of the stalk of a Weil sheaf at a geometric point is its stalk
Frobenius. -/
lemma WeilSheaf.stalkFunctor_obj_str_hom {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (σ : Spec (.of Ω) ⟶ Spec (.of Ω)) {x : Spec (.of Ω) ⟶ Z.left} (hx : x ≫ e.hom.left = σ ≫ x)
    (F : WeilSheaf ℓ e) :
    ((WeilSheaf.stalkFunctor ℓ e σ x hx).obj F).str.hom =
      stalkFrobenius ℓ (upperStarIsoIdOfIsSepClosed (Profinite.padicAlgClRingObj ℓ) σ) e hx
        F.str.hom := by
  rw [WeilSheaf.stalkFunctor_obj_str, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    weilStalkComparison_eq]
  rfl

/-- `weilPointComparison` is `pointComparison` for the underlying morphism of `e`. -/
lemma weilPointComparison_eq_pointComparison {x x' : P ⟶ Z.left} (h : x ≫ e.hom.left = σ ≫ x') :
    weilPointComparison ℓ τ e h = pointComparison _ τ e.hom.left h :=
  rfl

end StalkFrobenius

/-- The Frobenius transport `x̄'^* F ⟶ x̄^* F` of a Weil sheaf `F` for `e_X` between points with
`x̄ ≫ e_X = σ ≫ x̄'`: `weilPointComparison` followed by `x̄^* φ_F`. For `x̄' = x̄` it is the
Frobenius of the stalk of `F` at `x̄` (`stalkFrobenius`). -/
noncomputable def weilStalkTransport {x x' : P ⟶ X.left} (h : x ≫ eX.hom.left = σ ≫ x')
    (F : WeilSheaf ℓ eX) :
    (x')^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj F.carrier ⟶
      (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj F.carrier :=
  (weilPointComparison ℓ τ eX h).hom.app F.carrier ≫
    (x)^*⟦Profinite.padicAlgClRingObj ℓ⟧.map F.str.hom

/-- The Frobenius transport at a point fixed by the twisted Frobenius is the Frobenius of the
stalk. -/
lemma weilStalkTransport_self {x : P ⟶ X.left} (h : x ≫ eX.hom.left = σ ≫ x)
    (F : WeilSheaf ℓ eX) :
    weilStalkTransport ℓ eX τ h F = stalkFrobenius ℓ τ eX h F.str.hom :=
  rfl

/-- **The Frobenius of the stalk of a pushforward permutes the factors**: for a point `ȳ` with
`ȳ ≫ e_Y = σ ≫ ȳ` and points `x̄`, `x̄'` over `ȳ` with `x̄ ≫ e_X = σ ≫ x̄'`, the Frobenius of the
stalk of `f_* F` at `ȳ`, followed by the projection to the factor of `x̄`, is the projection to
the factor of `x̄'` followed by the Frobenius transport. -/
theorem stalkFrobenius_lowerStar_comp_stalkLowerStarProj {y : P ⟶ Y.left}
    (hy : y ≫ eY.hom.left = σ ≫ y) {x x' : P ⟶ X.left} (hx : x ≫ f.left = y)
    (hx' : x' ≫ f.left = y) (h : x ≫ eX.hom.left = σ ≫ x') (F : WeilSheaf ℓ eX) :
    stalkFrobenius ℓ τ eY hy ((weilSheafLowerStarComparison ℓ eX eY hf).hom.app F.carrier ≫
        (f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧.map F.str.hom) ≫
        stalkLowerStarProj _ hx F.carrier =
      stalkLowerStarProj _ hx' F.carrier ≫ weilStalkTransport ℓ eX τ h F := by
  rw [stalkFrobenius, weilStalkTransport, weilPointComparison_eq_pointComparison,
    weilPointComparison_eq_pointComparison, weilSheafLowerStarComparison_hom]
  exact pointComparison_lowerStarBaseChange_stalkLowerStarProj _ (commSq_left_of_comp_eq eX eY hf)
    τ hy hx hx' h F.carrier F.str.hom

/-- **The Frobenius trace on a stalk of a finite étale pushforward of Weil sheaves**: for a point
`ȳ` with `ȳ ≫ e_Y = σ ≫ ȳ`, `σ` an automorphism of `P ≅ Spec Ω`, the trace of the Frobenius of the
stalk of `f_* F` at `ȳ` is the sum of the traces of the Frobenius of the stalks of `F` at the
points `x̄` over `ȳ` with `x̄ ≫ e_X = σ ≫ x̄`, provided the stalks of `F` over `ȳ` are
dualizable. -/
theorem stalkFrobeniusTrace_lowerStar [IsFinite f.left] [Etale f.left] [IsIso σ]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (eP : P ≅ Spec (.of Ω))
    {y : P ⟶ Y.left} (hy : y ≫ eY.hom.left = σ ≫ y) (F : WeilSheaf ℓ eX)
    (hF : ∀ x : FibrePoints f.left y,
      Nonempty (HasRightDual ((x.1)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj F.carrier))) :
    stalkFrobeniusTrace ℓ τ eY hy
        ((weilSheafLowerStarComparison ℓ eX eY hf).hom.app F.carrier ≫
          (f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧.map F.str.hom) =
      ∑ᶠ x : {x : FibrePoints f.left y // x.1 ≫ eX.hom.left = σ ≫ x.1},
        stalkFrobeniusTrace ℓ τ eX x.2 F.str.hom := by
  classical
  have := finite_fibrePoints f.left y eP
  have := Fintype.ofFinite (FibrePoints f.left y)
  obtain ⟨hlim⟩ := isLimit_stalkLowerStarFan (Profinite.padicAlgClRingObj ℓ) f.left y eP F.carrier
  have hsq := (commSq_left_of_comp_eq eX eY hf).w
  rw [stalkFrobeniusTrace_eq, traceOrZero_eq_sum_of_isLimit_fan _ hlim hF _
    (fun x ↦ x.1 ≫ eX.hom.left = σ ≫ x.1) (fun x h ↦ stalkFrobenius ℓ τ eX h F.str.hom)
    (fun x h ↦ stalkFrobenius_lowerStar_comp_stalkLowerStarProj ℓ eX eY hf τ hy x.2 x.2 h F)
    (fun x h ↦ ⟨⟨inv σ ≫ x.1 ≫ eX.hom.left, by
      rw [Category.assoc, Category.assoc, hsq, ← Category.assoc x.1, x.2, hy,
        IsIso.inv_hom_id_assoc]⟩, fun he ↦ h (by
      have h' : inv σ ≫ x.1 ≫ eX.hom.left = x.1 := congrArg Subtype.val he
      calc x.1 ≫ eX.hom.left = σ ≫ inv σ ≫ x.1 ≫ eX.hom.left :=
            (IsIso.hom_inv_id_assoc σ _).symm
        _ = σ ≫ x.1 := by rw [h']), _,
      stalkFrobenius_lowerStar_comp_stalkLowerStarProj ℓ eX eY hf τ hy x.2 _
        (by rw [IsIso.hom_inv_id_assoc]) F⟩)]
  rw [← finsum_eq_sum_of_fintype]
  set G := fun x : FibrePoints f.left y ↦ if h : x.1 ≫ eX.hom.left = σ ≫ x.1 then
    traceOrZero (stalkFrobenius ℓ τ eX h F.str.hom) else 0 with hG
  have hR : (∑ᶠ x : {x : FibrePoints f.left y // x.1 ≫ eX.hom.left = σ ≫ x.1},
      stalkFrobeniusTrace ℓ τ eX x.2 F.str.hom) =
      ∑ᶠ x : {x : FibrePoints f.left y // x.1 ≫ eX.hom.left = σ ≫ x.1}, G x.1 :=
    finsum_congr fun x ↦ by dsimp only [G]; rw [dite_eq_left x.2]; rfl
  rw [hR, finsum_subtype_eq_finsum_cond]
  refine finsum_congr fun x ↦ ?_
  by_cases h : x.1 ≫ eX.hom.left = σ ≫ x.1
  · rw [finsum_eq_if, ite_eq_left h]
  · rw [finsum_eq_if, ite_eq_right h]
    dsimp only [G]
    rw [dite_eq_right h]


/-- Reindexing a sum of traces of stalk Frobenii over the fixed points along a family `pt`
enumerating them. -/
lemma finsum_stalkFrobeniusTrace_eq {y : P ⟶ Y.left} (G : WeilSheaf ℓ eX)
    {ι : Type*} (pt : ι → (P ⟶ X.left)) (hpt : ∀ i, pt i ≫ f.left = y)
    (hfix : ∀ i, pt i ≫ eX.hom.left = σ ≫ pt i) (hinj : Function.Injective pt)
    (hsurj : ∀ x : P ⟶ X.left, x ≫ f.left = y → x ≫ eX.hom.left = σ ≫ x → ∃ i, pt i = x) :
    ∑ᶠ i, stalkFrobeniusTrace ℓ τ eX (hfix i) G.str.hom =
      ∑ᶠ x : {x : FibrePoints f.left y // x.1 ≫ eX.hom.left = σ ≫ x.1},
        stalkFrobeniusTrace ℓ τ eX x.2 G.str.hom :=
  finsum_eq_of_bijective (fun i ↦ (⟨⟨pt i, hpt i⟩, hfix i⟩ :
      {x : FibrePoints f.left y // x.1 ≫ eX.hom.left = σ ≫ x.1}))
    ⟨fun _ _ hij ↦ hinj (congrArg (fun x ↦ x.1.1) hij), fun x ↦
      (hsurj x.1.1 x.1.2 x.2).imp fun _ hi ↦ Subtype.ext (Subtype.ext hi)⟩
    fun _ ↦ rfl

/-- The trace of the Frobenius of the stalk at `ȳ` of the pushforward `f_* G` of a Weil sheaf
along a finite étale morphism, as a sum over a family `pt : ι → (P ⟶ X)` enumerating the points
over `ȳ` fixed by the twisted Frobenius: `stalkFrobeniusTrace_lowerStar` for the structure
isomorphism of the Weil sheaf `f_* G`, reindexed along `pt`. -/
theorem stalkFrobeniusTrace_weilSheafLowerStar [IsFinite f.left] [Etale f.left]
    [IsIso σ] {Ω : Type u} [Field Ω] [IsSepClosed Ω] (eP : P ≅ Spec (.of Ω))
    {y : P ⟶ Y.left} (hy : y ≫ eY.hom.left = σ ≫ y) (G : WeilSheaf ℓ eX)
    (hG : ∀ x : FibrePoints f.left y,
      Nonempty (HasRightDual ((x.1)^*⟦Profinite.padicAlgClRingObj ℓ⟧.obj G.carrier)))
    {ι : Type*} (pt : ι → (P ⟶ X.left)) (hpt : ∀ i, pt i ≫ f.left = y)
    (hfix : ∀ i, pt i ≫ eX.hom.left = σ ≫ pt i) (hinj : Function.Injective pt)
    (hsurj : ∀ x : P ⟶ X.left, x ≫ f.left = y → x ≫ eX.hom.left = σ ≫ x → ∃ i, pt i = x) :
    stalkFrobeniusTrace ℓ τ eY hy ((weilSheafLowerStar ℓ eX eY hf).obj G).str.hom =
      ∑ᶠ i, stalkFrobeniusTrace ℓ τ eX (hfix i) G.str.hom := by
  have h : ((weilSheafLowerStar ℓ eX eY hf).obj G).str.hom =
      (weilSheafLowerStarComparison ℓ eX eY hf).hom.app G.carrier ≫
        (f.left)_*⟦Profinite.padicAlgClRingObj ℓ⟧.map G.str.hom := by
    rw [weilSheafLowerStar_obj_str, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [h, stalkFrobeniusTrace_lowerStar ℓ eX eY hf τ eP hy G hG]
  exact (finsum_stalkFrobeniusTrace_eq ℓ eX τ G pt hpt hfix hinj hsurj).symm

end AlgebraicGeometry.ProEtale.CondensedRing
