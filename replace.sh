git ls-files | xargs -n 1 sed -i '' 's/Data.Pair/Data.Tuple/g'
git ls-files | xargs -n 1 sed -i '' 's/[[:space:]]*$//g'
