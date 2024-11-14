


groupByH :: [Int] -> [Int] -> [[Int]]
groupByH [] acc@(_:_) = acc : []
groupByH [] [] = []
groupByH (n':ns) (n:acc) | n == n' = groupByH ns (n':acc)
                         | True    = acc : (groupByH (n':ns) [])
groupByH (n:ns) [] = groupByH ns [n]

groupBy :: [Int] -> [[Int]]
groupBy [] = []
groupBy (n:ns) = groupByH (n:ns) []
