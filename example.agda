module example where

open import Data.Bool
open import Data.Char
open import Data.List
open import Data.Maybe hiding (_>>=_)
open import Data.Nat.Show
open import Data.Product
open import Data.String hiding (_==_ ; _++_)
open import Data.Unit
open import Function
open import Codata.Musical.Costring

open import DataTypes
open import Parse hiding (_>>=_ ; _>>_)
open import RA

-- Schema for the cars table
Cars : Schema
Cars = ("pkey" , NAT)
     ∷ ("Model" , STR 20)
     ∷ ("Time" , STR 6)
     ∷ ("Wet"  , BOOL) ∷ []

-- Subset of the Cars schema that only has the Model column
Models : Schema
Models = ("Model" , STR 20) ∷ ("Time" , STR 6) ∷ []

-- Subset of the Cars schema that only has the Wet column
Wet : Schema
Wet = ("Wet" , BOOL) ∷ []

-- Generate the models schema from the cars schema
models : Handle Cars → RA Models
models h = Project Models {tt} (Read h)

-- Get the wet tests
wet : Handle Cars → RA Cars
wet h = Select ((Cars ! "Wet") {tt}) (Read h)

wetModels : Handle Cars → RA Models
wetModels h = Project Models {tt} (Select ((Cars ! "Wet") {tt}) (Read h))

-- This is a little inconvenient
mazda : String
mazda = "Mazda"

-- Take only Mazda cars
cool : Handle Cars → RA Cars
cool h = Select (((Cars ! "Model") {tt}) := Lit mazda) (Read h)

fast : Handle Cars → RA Cars
fast h = Select ((Cars ! "Time") {tt} :< Lit "2:12.3") (Read h)

slow : Handle Cars → RA Models
slow h = Project Models {tt} (Diff (Read h) (fast h))

nonWet : Handle Cars → RA Cars
nonWet h = Diff (Read h) (wet h)

union : Handle Cars → RA Cars
union h = Union (fast h) (Diff (Read h) (fast h))

prod : Handle Cars → RA (Models ++ Wet)
prod h = Product {p = tt}(Project Models {tt} (Read h)) (Project Wet {tt} (Read h))

open import IO.Primitive
import Foreign.Haskell as Hask

-- Monadic sequence
_>>_ : {A B : Set} → IO A → IO B → IO B
_>>_ a b = a >>= λ x → b
infixl 1 _>>_

-- Other namings of mapM like function are taken by the list
-- library.
mapM' : {A B : Set} → (A → IO B) → List A → IO ⊤
mapM' f xs = foldr (λ a b → f a >> b) (return tt) xs

printLine : String → IO ⊤
printLine = putStrLn ∘ toCostring

-- How many cars do better than a given time
test1 : IO ⊤
test1 = printLine "\n\nFast Cars" >>
        connect "cars" Cars  >>= λ h →
        putStrLn (toCostring (toSQL (fast h))) >>
        executeQuery (fast h) >>= λ res →
        mapM' (putStrLn ∘ toCostring ∘ showRow) res >>
        return tt

-- How long are the rows produced by the wet query
test2 : IO ⊤
test2 = printLine "\n\nNon wet cars" >>
        connect "cars" Cars  >>= λ h →
        putStrLn (toCostring (toSQL (nonWet h))) >>
        executeQuery (nonWet h) >>= λ res →
        mapM' (putStrLn ∘ toCostring ∘ showRow) res >>
        return tt

-- Select the slow cars and display their models/times
test3 : IO ⊤
test3 = printLine "\n\nSlow cars" >>
        connect "cars" Cars  >>= λ h →
        putStrLn (toCostring (toSQL (slow h))) >>
        executeQuery (slow h) >>= λ res →
        mapM' (putStrLn ∘ toCostring ∘ showRow) res >>
        return tt

test4 : IO ⊤
test4 = printLine "\n\nUnion of fast and slow cars" >>
        connect "cars" Cars  >>= λ h →
        putStrLn (toCostring (toSQL (union h))) >>
        executeQuery (union h) >>= λ res →
        mapM' (putStrLn ∘ toCostring ∘ showRow) res >>
        return tt

test5 : IO ⊤
test5 = printLine "\n\nProduct of Models with Wet" >>
        connect "cars" Cars  >>= λ h →
        putStrLn (toCostring (toSQL (prod h))) >>
        executeQuery (prod h) >>= λ res →
        mapM' (putStrLn ∘ toCostring ∘ showRow) res >>
        return tt

main : IO ⊤
main = test1 >> test2 >> test3 >> test4 >> test5
