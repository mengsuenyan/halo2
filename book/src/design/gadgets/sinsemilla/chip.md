# Chip for Sinsemilla

The aim of the design is to optimize the number of bits that can be processed for each step of the algorithm (which requires a doubling and addition in $\mathbb{G}$) for a given table size. Using a single table of size $2^k$ group elements, we can process $k$ bits at a time. See [Generic Lookups with PLONK](https://hackmd.io/LTPc5f-3S0qNF6MtwD-Tdg?view) for one way to implement the necessary lookups in a PLONK-like circuit model.

Note that it is slightly more efficient to express a double-and-add $[2] A + R$ as $(A + R) + A$.

## Constraint program
(Refer to: https://github.com/zcash/zcash/issues/3924)

Let $\mathcal{P} = \left\{(j,\, x_{P[j]},\, y_{P[j]}) \text{ for } j \in \{0..2^k - 1\}\right\}$.

Input: $z_n \in \{0..2^{kn} - 1\}$ such that $z_0 = 0$ and $z_{l+1} = \sum\limits_{i=0}^{l} m_i \cdot 2^{k(l - i)}$.

$z_0 = 0$
$(x_{A,0},\, y_{A,0}) = Q$
for $i$ from $0$ up to $n-1$:
    $(z_{i+1} - 2^k \cdot z_i,\, x_{P,i},\, y_{P,i}) \in \mathcal{P}$
    $\lambda_{1,i} \cdot (x_{A,i} - x_{P,i}) = y_{A,i} - y_{P,i}$
    $\lambda_{1,i}^2 = x_{R,i} + x_{A,i} + x_{P,i}$
    $(\lambda_{1,i} + \lambda_{2,i}) \cdot (x_{A,i} - x_{R,i}) = 2 y_{A,i}$
    $\lambda_{2,i}^2 = x_{A,i+1} + x_{R,i} + x_{A,i}$
    $\lambda_{2,i} \cdot (x_{A,i} - x_{A,i+1}) = y_{A,i} + y_{A,i+1}$

Output $(x_{A,n},\, y_{A,n})$


## PLONK / Halo 2 constraints

This uses one [lookup argument](https://hackmd.io/iOw7-HpFQY6dPF1aFY8pAw).

$$
\begin{array}{|c|c|c|c|c|c|c|c|c|c|c|c|c|}
\hline
\text{Step} &    x_A    &    y_A    &     z     &    \lambda_1    &   \lambda_2     &     m      &    x_P         &    y_P         &table_{idx}&    table_x     &   table_y      & \text{Gate} \\\hline
    0       & x_Q       & y_Q       &   0       & \lambda_{1,0}   & \lambda_{2,0}   &     m_0    & x_{P[m_0]}     & y_{P[m_0]}     &     0     & x_{P[0]}       & y_{P[0]}       & ECCLookup   \\\hline
    1       & x_{A,1}   & y_{A,1}   &   z_1     & \lambda_{1,1}   & \lambda_{2,1}   &     m_1    & x_{P[m_1]}     & y_{P[m_1]}     &     1     & x_{P[1]}       & y_{P[1]}       & ECCLookup   \\\hline
    2       & x_{A,2}   & y_{A,2}   &   z_2     & \lambda_{1,2}   & \lambda_{2,2}   &     m_2    & x_{P[m_2]}     & y_{P[m_2]}     &     2     & x_{P[2]}       & y_{P[2]}       & ECCLookup   \\\hline
  \vdots    & \vdots    & \vdots    &   \vdots  & \vdots          & \vdots          &    \vdots  & \vdots         & \vdots         &   \vdots  & \vdots         & \vdots         & \vdots      \\\hline
   n-1      & x_{A,n-1} & y_{A,n-1} &   z_{n-1} & \lambda_{1,n-1} & \lambda_{2,n-1} &   m_{n-1}  & x_{P[m_{n-1}]} & y_{P[m_{n-1}]} &   \vdots  & \vdots         & \vdots         & ECCLookup   \\\hline
    n       & x_{A,n}   & y_{A,n}   &   z_n     &                 &                 &            &                &                &   \vdots  & \vdots         & \vdots         &             \\\hline
  \vdots    &           &           &           &                 &                 &            &                &                &  2^k - 1  & x_{P[2^k - 1]} & y_{P[2^k - 1]} &             \\\hline
\end{array}
$$

### Specification of ECCLookup gate:

$$
\begin{array}{|c|l|}
\hline
\text{Degree} & \text{Constraint} \\\hline
3   & q_{ECC,i} \cdot \left(\lambda_{1,i} \cdot (x_{A,i} - x_{P,i}) - y_{A,i} + y_{P,i}\right) = 0 \\\hline
4   & q_{ECC,i} \cdot \left((\lambda_{1,i} + \lambda_{2,i}) \cdot (x_{A,i} - (\lambda_{1,i}^2 - x_{A,i} - x_{P,i})) - 2 y_{A,i}\right) = 0 \\\hline
3   & q_{ECC,i} \cdot \left(\lambda_{2,i}^2 - x_{A,i+1} - (\lambda_{1,i}^2 - x_{A,i} - x_{P,i}) - x_{A,i}\right) = 0 \\\hline
3   & q_{ECC,i} \cdot \left(\lambda_{2,i} \cdot (x_{A,i} - x_{A,i+1}) - y_{A,i} - y_{A,i+1}\right) = 0 \\\hline
\end{array}
$$

Plus:
- $q_Q \cdot \left(E_0 - x_Q\right) = 0$
- $q_Q \cdot \left(E_1 - y_Q\right) = 0$
- Lookup of columns $[m, x_P, y_P]$
- Check that $z_{l+1} = \sum\limits_{i=0}^{l} m_i \cdot 2^{k(l - i)}$ for each row
