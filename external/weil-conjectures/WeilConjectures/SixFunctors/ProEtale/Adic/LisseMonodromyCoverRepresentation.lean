/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyCoverLoop
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyCoverContinuity
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseCover.Transition
public import WeilConjectures.SixFunctors.ProEtale.Adic.TrivialDescent
public import WeilConjectures.RepresentationTheory.IntegralModel

/-!
# Lisse sheaves attached to representations, by descent along universal covers

Let `p : Ỹ_t ⟶ Y` be the universal cover at a geometric point `t` and `ρ` a continuous
finite-dimensional `ℚ̄_ℓ`-representation of `π₁(Y, t)`. Composing the matrix of `ρ` with the loop
map `Ỹ_t ×_Y Ỹ_t ⟶ π₁(Y, t)` (`AlgebraicGeometry.Scheme.UniversalCovers.loop`) gives a cocycle
of invertible matrices of locally finite functions on `Ỹ_t ×_Y Ỹ_t`; descending the trivial
sheaf `ℚ̄_ℓⁿ` on `Ỹ_t` along it gives a lisse sheaf on `Y` whose monodromy is `ρ`.

## Main statements

- `AlgebraicGeometry.Scheme.UniversalCovers.exists_lisseSheaf_rep`: every continuous
  finite-dimensional representation is the monodromy representation of a lisse sheaf, the
  descent (`AlgebraicGeometry.ProEtale.AdicSheaf.exists_iso_transitionMatrix_eq`) of the trivial
  sheaf along the loop cocycle.
- `AlgebraicGeometry.ProEtale.AdicSheaf.resOver_freeSection`: the restriction of sections of a
  trivialised sheaf along an endomorphism of the cover acts through the transition matrix.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Matrix

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

namespace AdicSheaf

section FreeSections

variable {V W : Scheme.{u}} {n : ℕ}

/-- The global section of `ℚ̄_ℓ,Vⁿ` given by a column of locally finite functions. -/
noncomputable def freeSection (f : Fin n → PadicAlgCl.locallyFiniteFunctions l V) :
    (Sheaf.Γ (Scheme.ProEt.topology V) (WeilCoefficients.{u} l)).obj
      (⨁ fun _ : Fin n ↦ unit l V).X :=
  ∑ i, ((Sheaf.Γ _ _).map (biproduct.ι (fun _ : Fin n ↦ unit l V) i).hom).hom
    (adicConstantGlobalSection (f i))

/-- The section of `ℚ̄_ℓ,V` given by a function is additive in the function. -/
lemma adicConstantGlobalSection_add (a b : PadicAlgCl.locallyFiniteFunctions l V) :
    adicConstantGlobalSection (a + b) =
      adicConstantGlobalSection a + adicConstantGlobalSection b := by
  rw [adicConstantGlobalSection, adicConstantGlobalSection, adicConstantGlobalSection,
    ← map_add]
  rfl

/-- The section of `ℚ̄_ℓ,V` given by a sum of functions. -/
lemma adicConstantGlobalSection_sum {ι : Type*} (s : Finset ι)
    (a : ι → PadicAlgCl.locallyFiniteFunctions l V) :
    adicConstantGlobalSection (∑ i ∈ s, a i) = ∑ i ∈ s, adicConstantGlobalSection (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, adicConstantGlobalSection]
    exact map_zero _
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx, adicConstantGlobalSection_add, ih]

/-- An endomorphism of the unit module multiplies sections by its function. -/
lemma Γ_map_adicConstantGlobalSection (ψ : unit l V ⟶ unit l V)
    (a : PadicAlgCl.locallyFiniteFunctions l V) :
    ((Sheaf.Γ _ _).map ψ.hom).hom (adicConstantGlobalSection a) =
      adicConstantGlobalSection (a * unitEndFun ψ) := by
  have n := congrArg (fun φ ↦ φ.hom (ULift.up a : (adicConstantSheaf l V).obj.obj
    (op (Scheme.ProEt.mk (𝟙 V))))) ((Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology V)
      (WeilCoefficients.{u} l) (Scheme.ProEt.isTerminalMkId V)).inv.naturality ψ.hom)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at n
  refine n.symm.trans ?_
  rw [adicConstantGlobalSection]
  congr 1
  exact adicConstantSheaf_app_eq_mul ψ.hom (unit_hom_linear ψ) _ _

/-- **A morphism of free modules acts on free sections through its matrix.** -/
lemma Γ_map_freeSection (T : (⨁ fun _ : Fin n ↦ unit l V) ⟶ ⨁ fun _ : Fin n ↦ unit l V)
    (f : Fin n → PadicAlgCl.locallyFiniteFunctions l V) :
    ((Sheaf.Γ _ _).map T.hom).hom (freeSection f) = freeSection (unitMatrix T *ᵥ f) := by
  let F := AdicSheaf.forget V ⋙ Sheaf.Γ (Scheme.ProEt.topology V) (WeilCoefficients.{u} l)
  have hF {M N : AdicSheaf l V} (φ : M ⟶ N) : (Sheaf.Γ _ _).map φ.hom = F.map φ := rfl
  have hι (i : Fin n) : biproduct.ι (fun _ : Fin n ↦ unit l V) i ≫ T =
      ∑ k, (biproduct.ι (fun _ : Fin n ↦ unit l V) i ≫ T ≫
        biproduct.π (fun _ : Fin n ↦ unit l V) k) ≫ biproduct.ι (fun _ : Fin n ↦ unit l V) k := by
    conv_lhs => rw [← Category.comp_id T, ← biproduct.total, Preadditive.comp_sum,
      Preadditive.comp_sum]
    simp only [Category.assoc]
  have step (i : Fin n) : ((Sheaf.Γ _ _).map T.hom).hom (((Sheaf.Γ _ _).map
      (biproduct.ι (fun _ : Fin n ↦ unit l V) i).hom).hom (adicConstantGlobalSection (f i))) =
      ∑ k, ((Sheaf.Γ _ _).map (biproduct.ι (fun _ : Fin n ↦ unit l V) k).hom).hom
        (adicConstantGlobalSection (unitMatrix T k i * f i)) := by
    rw [hF, hF, ← ConcreteCategory.comp_apply, ← F.map_comp, hι, F.map_sum]
    simp only [ModuleCat.hom_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [F.map_comp, ConcreteCategory.comp_apply]
    change ((Sheaf.Γ _ _).map (biproduct.ι (fun _ : Fin n ↦ unit l V) k).hom).hom
      (((Sheaf.Γ _ _).map (biproduct.ι (fun _ : Fin n ↦ unit l V) i ≫ T ≫
        biproduct.π (fun _ : Fin n ↦ unit l V) k).hom).hom (adicConstantGlobalSection (f i))) = _
    rw [Γ_map_adicConstantGlobalSection, mul_comm]
    rfl
  simp only [freeSection, map_sum, step]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← map_sum, Matrix.mulVec, dotProduct, adicConstantGlobalSection_sum]

/-- The pullback of the inclusion of a summand into a free module. -/
lemma adicUpperStar_map_ι_freeUpperStarIso_hom (g : W ⟶ V) (i : Fin n) :
    (g)^*ᵃ[l].map (biproduct.ι (fun _ : Fin n ↦ unit l V) i) ≫
        (freeUpperStarIso l (Fin n) g).hom =
      (adicUpperStarUnitIso l g).hom ≫ biproduct.ι (fun _ : Fin n ↦ unit l W) i := by
  have h1 : biproduct.ι (fun _ : Fin n ↦ unit l W) i ≫ (freeUpperStarIso l (Fin n) g).inv =
      (adicUpperStarUnitIso l g).inv ≫
        (g)^*ᵃ[l].map (biproduct.ι (fun _ : Fin n ↦ unit l V) i) := by
    simp [freeUpperStarIso]
  rw [← Iso.inv_comp_eq, ← Category.assoc, ← h1, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- **Restriction of free sections**: the restriction along `g : W ⟶ V` of the free section of a
column of functions, identified with a section of `ℚ̄_ℓ,Wⁿ`, is the free section of the
pulled back column. -/
lemma globalSectionsToUpperStar_freeSection (g : W ⟶ V)
    (f : Fin n → PadicAlgCl.locallyFiniteFunctions l V) :
    ((Sheaf.Γ _ _).map (freeUpperStarIso l (Fin n) g).hom.hom).hom
        (((globalSectionsToUpperStar _ g).app (⨁ fun _ : Fin n ↦ unit l V).X).hom
          (freeSection f)) =
      freeSection fun i ↦ PadicAlgCl.locallyFiniteFunctionsComp l g.base.hom (f i) := by
  simp only [freeSection, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have key : (Sheaf.Γ _ _).map (biproduct.ι (fun _ : Fin n ↦ unit l V) i).hom ≫
      (globalSectionsToUpperStar _ g).app (⨁ fun _ : Fin n ↦ unit l V).X ≫
        (Sheaf.Γ _ _).map (freeUpperStarIso l (Fin n) g).hom.hom =
      (globalSectionsToUpperStar _ g).app (adicConstantSheaf l V) ≫
        (Sheaf.Γ _ _).map (adicUpperStarUnitIso l g).hom.hom ≫
          (Sheaf.Γ _ _).map (biproduct.ι (fun _ : Fin n ↦ unit l W) i).hom := by
    have n := (globalSectionsToUpperStar (WeilCoefficients.{u} l) g).naturality
      (biproduct.ι (fun _ : Fin n ↦ unit l V) i).hom
    rw [← Category.assoc, n, Functor.comp_map, Category.assoc, ← Functor.map_comp,
      ← Functor.map_comp]
    have e := congrArg Mod.Hom.hom (adicUpperStar_map_ι_freeUpperStarIso_hom (l := l) g i)
    rw [Mod.comp_hom', Mod.comp_hom', adicUpperStar_map_hom] at e
    rw [e]
    rfl
  have := congrArg (fun φ ↦ φ.hom (adicConstantGlobalSection (f i))) key
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at this
  refine this.trans ?_
  congr 1
  exact globalSectionsToUpperStar_adicConstantGlobalSection g (f i)
end FreeSections

section Restriction

variable {Y W : Scheme.{u}} {G : AdicSheaf l Y} {p : W ⟶ Y} {n : ℕ}
  (ε : (p)^*ᵃ[l].obj G ≅ ⨁ fun _ : Fin n ↦ unit l W)

/-- The trivialisation `p^* G ≅ (𝟙 ≫ p)^* G ≅ ℚ̄_ℓⁿ` obtained by pulling back `ε` along the
identity, whose restrictions along endomorphisms of `W` over `Y` are computed by transition
matrices. -/
noncomputable def trivId : (p)^*ᵃ[l].obj G ≅ ⨁ fun _ : Fin n ↦ unit l W :=
  (adicUpperStarCongr l (Category.id_comp p)).symm.app G ≪≫ trivPull p ε (𝟙 W)

/-- The pullback along a morphism `c` of a congruence isomorphism, conjugated by the composition
isomorphisms. -/
lemma adicUpperStarComp_hom_app_comp_map_congr_comp_inv_app {Q X Z : Scheme.{u}} (c : Q ⟶ X)
    {x y : X ⟶ Z} (q : x = y) (q' : c ≫ x = c ≫ y) (M : AdicSheaf l Z) :
    (adicUpperStarComp l c x).hom.app M ≫ (c)^*ᵃ[l].map ((adicUpperStarCongr l q).hom.app M) ≫
        (adicUpperStarComp l c y).inv.app M =
      (adicUpperStarCongr l q').hom.app M := by
  rw [← adicUpperStarComp_inv_app_comp_congr_comp_hom_app c q q' M]
  simp

/-- **The restriction along an endomorphism `h` of `W` over `Y`**, in the trivialisation
`trivId ε`, is the pullback along `h` followed by the transition morphism of `h, 𝟙`. -/
lemma trivId_conj (h : W ⟶ W) (e : h ≫ p = p) :
    (freeUpperStarIso l (Fin n) h).inv ≫ (h)^*ᵃ[l].map (trivId ε).inv ≫
        (adicUpperStarComp l h p).inv.app G ≫ (adicUpperStarCongr l e).hom.app G ≫
          (trivId ε).hom =
      transitionHom ε (h ≫ 𝟙 W) (𝟙 W) (by rw [Category.comp_id, e, Category.id_comp]) := by
  have h₁ := trivPull_comp_hom ε h (𝟙 W)
  have hε₁ : (trivId ε).inv = (trivPull p ε (𝟙 W)).inv ≫
      (adicUpperStarCongr l (Category.id_comp p)).hom.app G := rfl
  have hε₂ : (trivId ε).hom = (adicUpperStarCongr l (Category.id_comp p)).inv.app G ≫
      (trivPull p ε (𝟙 W)).hom := rfl
  rw [transitionHom_eq, ← cancel_epi (trivPull p ε (h ≫ 𝟙 W)).hom, Iso.hom_inv_id_assoc, h₁]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [hε₁, Functor.map_comp]
  simp only [Category.assoc]
  rw [Iso.hom_inv_id_map_assoc, reassoc_of% (adicUpperStarComp_hom_app_comp_map_congr_comp_inv_app h
      (Category.id_comp p) (by rw [Category.id_comp]) G), hε₂,
    adicUpperStarCongr_inv_app (Category.id_comp p) (Category.id_comp p).symm,
    reassoc_of% adicUpperStarCongr_hom_app_trans, reassoc_of% adicUpperStarCongr_hom_app_trans,
    reassoc_of% adicUpperStarCongr_hom_app_trans]
  all_goals simp [e]

/-- **Restriction of sections in a trivialisation.** The restriction of sections of `p^* G`
along an endomorphism `h` of `W` over `Y`, in the coordinates of `trivId ε`, pulls back the
column of functions along `h` and multiplies it by the transition matrix of `h, 𝟙`. -/
lemma resOver_freeSection (h : W ⟶ W) (e : h ≫ p = p)
    (f : Fin n → PadicAlgCl.locallyFiniteFunctions l W) :
    ((Sheaf.Γ _ _).map (trivId ε).hom.hom).hom (((resOver _ h e).app G.X).hom
      (((Sheaf.Γ _ _).map (trivId ε).inv.hom).hom (freeSection f))) =
      freeSection (unitMatrix (transitionHom ε (h ≫ 𝟙 W) (𝟙 W)
        (by rw [Category.comp_id, e, Category.id_comp])) *ᵥ
          fun i ↦ PadicAlgCl.locallyFiniteFunctionsComp l h.base.hom (f i)) := by
  rw [← trivId_conj ε h e, ← Γ_map_freeSection, ← globalSectionsToUpperStar_freeSection]
  have nat : (Sheaf.Γ _ _).map (trivId ε).inv.hom ≫ (globalSectionsToUpperStar _ h).app
      ((p)^*[WeilCoefficients.{u} l].obj G.X) =
      (globalSectionsToUpperStar _ h).app (⨁ fun _ : Fin n ↦ unit l W).X ≫
        ((h)^*[WeilCoefficients.{u} l] ⋙ Sheaf.Γ _ _).map (trivId ε).inv.hom :=
    (globalSectionsToUpperStar (WeilCoefficients.{u} l) h).naturality (trivId ε).inv.hom
  have key : (Sheaf.Γ _ _).map (trivId ε).inv.hom ≫ (resOver _ h e).app G.X ≫
      (Sheaf.Γ _ _).map (trivId ε).hom.hom =
      (globalSectionsToUpperStar _ h).app (⨁ fun _ : Fin n ↦ unit l W).X ≫
        (Sheaf.Γ _ _).map (freeUpperStarIso l (Fin n) h).hom.hom ≫
          (Sheaf.Γ _ _).map ((freeUpperStarIso l (Fin n) h).inv ≫ (h)^*ᵃ[l].map (trivId ε).inv ≫
            (adicUpperStarComp l h p).inv.app G ≫ (adicUpperStarCongr l e).hom.app G ≫
              (trivId ε).hom).hom := by
    rw [resOver_app, upperStarFactor_inv_app]
    simp only [Category.assoc]
    rw [reassoc_of% nat]
    refine congrArg (_ ≫ ·) ?_
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    refine congrArg (Sheaf.Γ _ _).map ?_
    rw [← Mod.comp_hom' (freeUpperStarIso l (Fin n) h).hom, Iso.hom_inv_id_assoc]
    simp only [Mod.comp_hom', adicUpperStar_map_hom, adicUpperStarComp_inv_app_hom,
      adicUpperStarCongr_hom_app_hom, Category.assoc]
  exact congrArg (fun φ ↦ φ.hom (freeSection f)) key

end Restriction

section Constant

variable {W : Scheme.{u}} {n : ℕ}

/-- The section of `ℚ̄_ℓ,Wⁿ` given by a vector of constants. -/
noncomputable def constSection (c : Fin n → PadicAlgCl l) :
    (Sheaf.Γ (Scheme.ProEt.topology W) (WeilCoefficients.{u} l)).obj
      (⨁ fun _ : Fin n ↦ unit l W).X :=
  freeSection fun i ↦ algebraMap _ _ (c i)

/-- The projections of free sections. -/
lemma Γ_map_π_freeSection (f : Fin n → PadicAlgCl.locallyFiniteFunctions l W) (j : Fin n) :
    ((Sheaf.Γ _ _).map (biproduct.π (fun _ : Fin n ↦ unit l W) j).hom).hom (freeSection f) =
      adicConstantGlobalSection (f j) := by
  classical
  simp only [freeSection, map_sum]
  rw [Finset.sum_eq_single j]
  · rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Mod.comp_hom', biproduct.ι_π_self,
      Mod.id_hom', CategoryTheory.Functor.map_id]
    rfl
  · intro i _ hij
    let F := AdicSheaf.forget W ⋙ Sheaf.Γ (Scheme.ProEt.topology W) (WeilCoefficients.{u} l)
    change (F.map (biproduct.π (fun _ : Fin n ↦ unit l W) j)).hom
      ((F.map (biproduct.ι (fun _ : Fin n ↦ unit l W) i)).hom _) = 0
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, biproduct.ι_π_ne _ hij, F.map_zero]
    rfl
  · simp

/-- Every section of `ℚ̄_ℓ,V` is the section of a function. -/
lemma exists_adicConstantGlobalSection_eq
    (x : (Sheaf.Γ (Scheme.ProEt.topology W) (WeilCoefficients.{u} l)).obj (adicConstantSheaf l W)) :
    ∃ a, adicConstantGlobalSection a = x := by
  refine ⟨(((Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology W) (WeilCoefficients.{u} l)
    (Scheme.ProEt.isTerminalMkId W)).hom.app (adicConstantSheaf l W)).hom x).down, ?_⟩
  rw [adicConstantGlobalSection, ULift.up_down, ← ConcreteCategory.comp_apply,
    Iso.hom_inv_id_app]
  rfl

/-- On a connected scheme, the sections of a vector of constants are all the sections of
`ℚ̄_ℓ,Wⁿ`. -/
lemma bijective_constSection [ConnectedSpace W] :
    Function.Bijective (constSection (l := l) (W := W) (n := n)) := by
  classical
  refine ⟨fun c c' h ↦ funext fun j ↦ ?_, fun x ↦ ?_⟩
  · have := congrArg ((Sheaf.Γ _ _).map (biproduct.π (fun _ : Fin n ↦ unit l W) j).hom).hom h
    rw [constSection, constSection, Γ_map_π_freeSection, Γ_map_π_freeSection] at this
    have := congrArg (fun f : PadicAlgCl.locallyFiniteFunctions l W ↦
      f.1 (Classical.arbitrary W)) (adicConstantGlobalSection_injective this)
    simpa using this
  · choose a ha using fun i ↦ exists_adicConstantGlobalSection_eq (l := l) (W := W)
      (((Sheaf.Γ _ _).map (biproduct.π (fun _ : Fin n ↦ unit l W) i).hom).hom x)
    refine ⟨fun i ↦ (a i).1 (Classical.arbitrary W), ?_⟩
    have hx : x = ∑ i, ((Sheaf.Γ _ _).map (biproduct.ι (fun _ : Fin n ↦ unit l W) i).hom).hom
        (((Sheaf.Γ _ _).map (biproduct.π (fun _ : Fin n ↦ unit l W) i).hom).hom x) := by
      let F := AdicSheaf.forget W ⋙ Sheaf.Γ (Scheme.ProEt.topology W) (WeilCoefficients.{u} l)
      have e := congrArg (fun φ ↦ (F.map φ).hom x) (biproduct.total
        (f := fun _ : Fin n ↦ unit l W))
      simp only [CategoryTheory.Functor.map_id, F.map_sum, ModuleCat.hom_sum,
        LinearMap.sum_apply, F.map_comp] at e
      exact e.symm
    rw [hx, constSection, freeSection]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← ha i, ← PadicAlgCl.locallyFiniteFunctions_eq_algebraMap]

end Constant

end AdicSheaf

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.Scheme.UniversalCovers

open ProEtale FiniteEtale AdicSheaf

variable {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}} {Ω : Type u} [Field Ω]
  {U : Scheme.UniversalCovers Y Ω}

section Cocycle

variable (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) {n : ℕ}
  (R : Aut (fiber t) →* Matrix (Fin n) (Fin n) (PadicAlgCl l))
  (hR : ∀ i j, Continuous fun g ↦ R g i j)

/-- **The loop cocycle of a matrix representation** `R` of `π₁(Y, t)`: the matrix of locally
finite functions `q ↦ R (loop q)` on `Ỹ_t ×_Y Ỹ_t`. Its entries are locally finite since the
matrix coefficients of `R` lie in a finite extension of `ℚ_ℓ`. -/
noncomputable def loopMatrix : Matrix (Fin n) (Fin n)
    (PadicAlgCl.locallyFiniteFunctions l ↥(Limits.pullback (U.proj t) (U.proj t))) :=
  fun i j ↦ ⟨⟨fun q ↦ R (U.loop t q) i j, (hR i j).comp (U.continuous_loop t)⟩, by
    obtain ⟨E, hE, hmem⟩ := PadicAlgCl.exists_finiteDimensional_forall_mem l R hR
    have : FiniteDimensional ℚ_[l] (Subalgebra.toSubmodule E.toSubalgebra) := hE
    intro x
    refine ⟨Set.univ, Filter.univ_mem, Submodule.finiteDimensional_of_le
      (S₂ := Subalgebra.toSubmodule E.toSubalgebra) (Submodule.span_le.2 ?_)⟩
    rintro _ ⟨q, -, rfl⟩
    exact hmem _ i j⟩

/-- The entries of the loop cocycle. -/
lemma loopMatrix_apply (i j : Fin n) (q : ↥(Limits.pullback (U.proj t) (U.proj t))) :
    (loopMatrix (U := U) t R hR i j).1 q = R (U.loop t q) i j :=
  rfl

/-- The loop cocycle is trivial on the diagonal. -/
lemma loopMatrix_diagonal :
    (loopMatrix (U := U) t R hR).map (PadicAlgCl.locallyFiniteFunctionsComp l
      (pullback.diagonal (U.proj t)).base.hom) = 1 := by
  ext i j : 1
  refine Subtype.ext (ContinuousMap.ext fun x ↦ ?_)
  simp only [Matrix.map_apply, PadicAlgCl.locallyFiniteFunctionsComp_apply_coe,
    ContinuousMap.comp_apply, loopMatrix_apply]
  rw [loop_diagonal, map_one, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

/-- The loop cocycle satisfies the cocycle condition. -/
lemma loopMatrix_cocycle :
    (loopMatrix (U := U) t R hR).map
        (PadicAlgCl.locallyFiniteFunctionsComp l (tripleProj₁₃ (U.proj t)).base.hom) =
      (loopMatrix (U := U) t R hR).map (PadicAlgCl.locallyFiniteFunctionsComp l
        (pullback.snd (pullback.snd (U.proj t) (U.proj t))
          (pullback.fst (U.proj t) (U.proj t))).base.hom) *
      (loopMatrix (U := U) t R hR).map (PadicAlgCl.locallyFiniteFunctionsComp l
        (pullback.fst (pullback.snd (U.proj t) (U.proj t))
          (pullback.fst (U.proj t) (U.proj t))).base.hom) := by
  ext i j : 1
  refine Subtype.ext (ContinuousMap.ext fun τ ↦ ?_)
  simp only [Matrix.map_apply, Matrix.mul_apply, PadicAlgCl.locallyFiniteFunctionsComp_apply_coe,
    ContinuousMap.comp_apply, loopMatrix_apply]
  rw [loop_tripleProj₁₃, map_mul, Matrix.mul_apply]
  simp only [AddSubmonoidClass.coe_finsetSum, ContinuousMap.sum_apply, MulMemClass.coe_mul,
    ContinuousMap.mul_apply, PadicAlgCl.locallyFiniteFunctionsComp_apply_coe,
    ContinuousMap.comp_apply, loopMatrix_apply]

end Cocycle

section Rep

variable (hU : ∀ (y : Spec (.of (AlgebraicClosure Ω)) ⟶ Y) (G : LisseSheaf l Y), ∃ n : ℕ,
    Nonempty ((U.proj y)^*ᵃ[l].obj G.obj ≅ ⨁ fun _ : Fin n ↦ AdicSheaf.unit l (U.cover y)))

/-- The sections of a vector of constants, as a `ℚ̄_ℓ`-linear map. -/
noncomputable def constSectionLinearMap (W : Scheme.{u}) (n : ℕ) :
    (Fin n → PadicAlgCl l) →ₗ[PadicAlgCl l] (WeilCoefficients.toModuleCat l).obj
      ((Sheaf.Γ (Scheme.ProEt.topology W) (WeilCoefficients.{u} l)).obj
        (⨁ fun _ : Fin n ↦ unit l W).X) where
  toFun := constSection
  map_add' c c' := by
    simp only [constSection, freeSection, Pi.add_apply, map_add, adicConstantGlobalSection_add,
      Finset.sum_add_distrib]
  map_smul' a c := by
    rw [RingHom.id_apply, ModuleCat.restrictScalars.smul_def]
    simp only [constSection, freeSection, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← map_smul]
    congr 1
    rw [adicConstantGlobalSection, adicConstantGlobalSection]
    rw [← LinearMap.map_smul ((Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology W)
      (WeilCoefficients.{u} l) (Scheme.ProEt.isTerminalMkId W)).inv.app
        (adicConstantSheaf l W)).hom]
    congr 1

include hU in
/-- **Every continuous finite-dimensional representation is a monodromy representation**, for
the monodromy from universal covers on which lisse sheaves are free. The lisse sheaf attached
to `ρ` is the descent of `ℚ̄_ℓⁿ` along the universal cover `p : Ỹ_t ⟶ Y` for the loop cocycle
of the matrix of `ρ` (`AlgebraicGeometry.Scheme.UniversalCovers.loopMatrix`,
`AlgebraicGeometry.ProEtale.AdicSheaf.exists_iso_transitionMatrix_eq`): in the coordinates of
the trivialisation over `Ỹ_t`, the transport along a loop `g` is the restriction along
`(transport g)⁻¹`, which acts on constant sections by the transition matrix along the graph of
`g`, that is by the matrix of `ρ(g)`
(`AlgebraicGeometry.ProEtale.AdicSheaf.resOver_freeSection`). -/
theorem exists_lisseSheaf_rep (t : Spec (.of (AlgebraicClosure Ω)) ⟶ Y)
    (V : Type (u + 1)) [AddCommGroup V] [Module (PadicAlgCl l) V]
    [FiniteDimensional (PadicAlgCl l) V] (ρ : Representation (PadicAlgCl l) (Aut (fiber t)) V)
    (hρ : ∀ (φ : Module.Dual (PadicAlgCl l) V) (v : V), Continuous fun g ↦ φ (ρ g v)) :
    ∃ (G : LisseSheaf l Y) (e : LisseMonodromy.StalkSpace t G ≃ₗ[PadicAlgCl l] V),
      ∀ g v, e ((U.lisseMonodromy hU).rep t G g v) = ρ g (e v) := by
  classical
  set n := Module.finrank (PadicAlgCl l) V
  let b := Module.finBasis (PadicAlgCl l) V
  let R : Aut (fiber t) →* Matrix (Fin n) (Fin n) (PadicAlgCl l) :=
    { toFun g := LinearMap.toMatrix b b (ρ g)
      map_one' := by rw [map_one, LinearMap.toMatrix_one]
      map_mul' g h := by rw [map_mul, LinearMap.toMatrix_mul] }
  have hR (i j : Fin n) : Continuous fun g ↦ R g i j := by
    simp only [R, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.toMatrix_apply]
    exact hρ (b.coord i) (b j)
  have := U.weaklyEtale_proj t
  have : Surjective (U.proj t) := ⟨U.surjective_proj t⟩
  have := U.quasiCompact_proj t
  have := U.connectedSpace t
  obtain ⟨G, ε, hε⟩ := exists_iso_transitionMatrix_eq (U.proj t) (loopMatrix (U := U) t R hR)
    (loopMatrix_diagonal t R hR) (loopMatrix_cocycle t R hR)
  have hG : IsAdicLisseSheaf G := ⟨Presieve.singleton (U.proj t),
    Scheme.Hom.singleton_mem_propQCPrecoverage (P := @WeaklyEtale) inferInstance,
    fun V f hf ↦ by cases hf; exact ⟨n, ⟨ε⟩⟩⟩
  let G' : LisseSheaf l Y := ⟨G, hG⟩
  -- the linear map `ℚ̄_ℓⁿ → G_t` of constant sections over `Ỹ_t`
  let Ψ : (Fin n → PadicAlgCl l) →ₗ[PadicAlgCl l] LisseMonodromy.StalkSpace t G' :=
    ((WeilCoefficients.toModuleCat l).map ((U.ptRes l t).app G.X)).hom ∘ₗ
      ((WeilCoefficients.toModuleCat l).map ((Sheaf.Γ _ _).map (trivId ε).inv.hom)).hom ∘ₗ
        constSectionLinearMap (U.cover t) n
  have hΨ : Function.Bijective Ψ := by
    have := isIso_ptRes_app hU t G'
    refine (ConcreteCategory.bijective_of_isIso ((U.ptRes l t).app G.X)).comp
      ((ConcreteCategory.bijective_of_isIso ((Sheaf.Γ _ _).map (trivId ε).inv.hom)).comp
        bijective_constSection)
  -- the monodromy acts on constant sections through `R`
  have hrep (g : Aut (fiber t)) (c : Fin n → PadicAlgCl l) :
      (U.lisseMonodromy hU).rep t G' g (Ψ c) = Ψ (R g *ᵥ c) := by
    rw [LisseMonodromy.rep_apply, LisseMonodromy.monoLinear, lisseMonodromy_mono]
    change ((monoIso hU g.asIso).hom.app G').hom (((U.ptRes l t).app G.X).hom _) = _
    rw [monoIso_hom_app_ptRes_apply, transportRes_hom_app]
    change ((U.ptRes l t).app G.X).hom _ = ((U.ptRes l t).app G.X).hom _
    congr 1
    set h := (U.transport g.asIso).inv
    have he : h ≫ U.proj t = U.proj t := U.transport_inv_proj g.asIso
    have key := resOver_freeSection ε h he fun i ↦ algebraMap _ _ (c i)
    -- the transition matrix of `h, 𝟙` is the constant matrix `R g`
    let c' : U.cover t ⟶ Limits.pullback (U.proj t) (U.proj t) :=
      pullback.lift (h ≫ 𝟙 _) (𝟙 _) (by rw [Category.comp_id, Category.id_comp, he])
    have hc'snd : c' ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have : WeaklyEtale (c' ≫ pullback.snd (U.proj t) (U.proj t)) := by
      rw [hc'snd]; infer_instance
    have : WeaklyEtale c' := WeaklyEtale.of_comp c' (pullback.snd (U.proj t) (U.proj t))
    have hab₀ : (h ≫ 𝟙 _) ≫ U.proj t = 𝟙 _ ≫ U.proj t := by simp [he]
    have hT : unitMatrix (transitionHom ε (h ≫ 𝟙 _) (𝟙 _) hab₀) =
        (R g).map (algebraMap _ _) := by
      change transitionMatrix ε (h ≫ 𝟙 _) (𝟙 _) hab₀ = _
      rw [transitionMatrix_congr ε (pullback.lift_fst (h ≫ 𝟙 _) (𝟙 _) hab₀).symm
        (pullback.lift_snd (h ≫ 𝟙 _) (𝟙 _) hab₀).symm
        hab₀ (by rw [Category.assoc, Category.assoc, pullback.condition]),
        transitionMatrix_comp ε c' _ _ pullback.condition
          (by rw [Category.assoc, Category.assoc, pullback.condition]), hε]
      ext i j : 1
      refine Subtype.ext (ContinuousMap.ext fun x ↦ ?_)
      simp only [Matrix.map_apply, PadicAlgCl.locallyFiniteFunctionsComp_apply_coe,
        ContinuousMap.comp_apply, loopMatrix_apply]
      rw [loop_apply_of_eq_comp t c' (h ≫ 𝟙 _) g (pullback.hom_ext (by simp [c', graph_fst])
        (by simp [c', graph_snd, h]))]
      rfl
    have hconst : (fun i ↦ PadicAlgCl.locallyFiniteFunctionsComp l h.base.hom
        (algebraMap (PadicAlgCl l) _ (c i))) = fun i ↦ algebraMap _ _ (c i) := rfl
    rw [hT, hconst] at key
    have hmul : (R g).map (algebraMap (PadicAlgCl l)
        (PadicAlgCl.locallyFiniteFunctions l (U.cover t))) *ᵥ (fun i ↦ algebraMap _ _ (c i)) =
        fun i ↦ algebraMap _ _ ((R g *ᵥ c) i) := by
      funext i
      exact (RingHom.map_mulVec (algebraMap _ _) (R g) c i).symm
    rw [hmul] at key
    change ((Sheaf.Γ _ _).map (trivId ε).inv.hom ≫ (resOver _ h he).app G.X).hom
      (freeSection fun i ↦ algebraMap _ _ (c i)) = ((Sheaf.Γ _ _).map (trivId ε).inv.hom).hom
        (freeSection fun i ↦ algebraMap (PadicAlgCl l)
          (PadicAlgCl.locallyFiniteFunctions l (U.cover t)) ((R g *ᵥ c) i))
    have hid (x : (Sheaf.Γ (Scheme.ProEt.topology (U.cover t)) (WeilCoefficients.{u} l)).obj
        ((U.proj t)^*ᵃ[l].obj G).X) :
        ((Sheaf.Γ _ _).map (trivId ε).inv.hom).hom (((Sheaf.Γ _ _).map (trivId ε).hom.hom).hom x) =
          x := by
      rw [← ModuleCat.comp_apply, ← Functor.map_comp, ← Mod.comp_hom', Iso.hom_inv_id,
        Mod.id_hom', CategoryTheory.Functor.map_id]
      rfl
    rw [← key, hid]
    rfl
  refine ⟨G', (LinearEquiv.ofBijective Ψ hΨ).symm.trans b.equivFun.symm, fun g v ↦ ?_⟩
  obtain ⟨c, rfl⟩ := hΨ.2 v
  rw [hrep, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.ofBijective_symm_apply_apply, LinearEquiv.ofBijective_symm_apply_apply]
  apply b.equivFun.injective
  rw [LinearEquiv.apply_symm_apply, Module.Basis.equivFun_apply,
    ← LinearMap.toMatrix_mulVec_repr b b, ← Module.Basis.equivFun_apply,
    LinearEquiv.apply_symm_apply]
  rfl
end Rep

end AlgebraicGeometry.Scheme.UniversalCovers
