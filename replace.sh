git ls-files | xargs -n 1 sed -i '' 's/Semigroup:Monoid/Semigroup:Monoid/g'
git ls-files | xargs -n 1 sed -i '' 's/[[:space:]]*$//g'
