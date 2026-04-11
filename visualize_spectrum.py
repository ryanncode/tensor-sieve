import csv
import matplotlib.pyplot as plt
import sys
import os

def main():
    if not os.path.exists('data.csv'):
        print("data.csv not found. Did you run `lake exe tensor_sieve > data.csv`?")
        sys.exit(1)
        
    xs = []
    spacings = []
    
    with open('data.csv', 'r') as f:
        reader = csv.DictReader(f)
        for row in reader:
            xs.append(int(row['x']))
            # We use local_degree as the analog for spectral weight/divergence
            deg = int(row['local_degree'])
            spacings.append(deg)

    if not xs:
        print("No data found.")
        sys.exit(1)

    plt.figure(figsize=(12, 6))
    
    # Plot 1: Trace Formula Convergence (Cumulative Zeros / Energy Levels)
    plt.subplot(1, 2, 1)
    # We plot the trajectory of the sieve
    levels = range(1, len(xs) + 1)
    plt.plot(levels, xs, marker='.', linestyle='-', color='red')
    plt.title('Non-Archimedean Sieve Trajectory')
    plt.xlabel('Contraction Step')
    plt.ylabel('Semantic Address (x)')
    plt.yscale('log')
    plt.grid(True)
    
    # Plot 2: Eigenvalue Spacing Distribution (Arithmetic Divergence)
    plt.subplot(1, 2, 2)
    plt.hist(spacings, bins=max(10, len(set(spacings))), alpha=0.7, color='blue', edgecolor='black')
    plt.title('Arithmetic Divergence (Local Degree)')
    plt.xlabel('Local Degree (D)')
    plt.ylabel('Frequency')
    plt.grid(True)
    
    plt.tight_layout()
    plt.savefig('spectrum_visualization.png')
    print("Saved visualization to spectrum_visualization.png")

if __name__ == '__main__':
    main()
